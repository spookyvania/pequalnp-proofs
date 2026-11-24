import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1645

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_value' {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    value ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then value ⟨gs, 0⟩ x r else false) := by
  have h := gate_value ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def V {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool := value ⟨gs, 0⟩ x w

lemma V_eval {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) :
    V gs x w = Circuit.eval ⟨gs, w⟩ (List.ofFn x) := rfl

lemma V_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    V gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then V gs x r else false) :=
  gate_value' gs x k hk

lemma V_missing {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : V gs x w = false :=
  missing_value ⟨gs, 0⟩ x w hw

lemma V_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    V gs x w = x ⟨w, hw⟩ := by
  change (run gs (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hp : w < (List.ofFn x).length := by simpa using hw
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma get_idx {α : Type} (l : List α) (i : Fin l.length) : l.get i = l[i.val] := rfl

lemma not_head {n : ℕ} (gs : List Gate) (j h : Fin gs.length)
    (hop : (gs.get j).op = GateOp.not) (hlt : h < j)
    (hr : ∃ r : List ℕ, (gs.get j).inputs = (n + (h : ℕ)) :: r) (x : Fin n → Bool) :
    V gs x (n + (j : ℕ)) = !(V gs x (n + (h : ℕ))) := by
  obtain ⟨r, hr⟩ := hr
  have hk : (j : ℕ) < gs.length := j.isLt
  rw [V_gate gs x (j : ℕ) hk]
  have hop' : gs[(j : ℕ)].op = GateOp.not := by simpa [get_idx] using hop
  have hr' : gs[(j : ℕ)].inputs = (n + (h : ℕ)) :: r := by simpa [get_idx] using hr
  rw [hop', hr']
  simp [GateOp.eval, hlt]

lemma monoEarly {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (hops : ∀ gt ∈ gs, (gt.op = GateOp.and ∨ gt.op = GateOp.or ∨ gt.op = GateOp.not) ∧
      gt.inputs.length ≤ 2)
    (honly : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ w, w < n + (j : ℕ) → V gs x w = true → V gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hn : w < n
    · rw [V_input gs x w hn] at hx
      rw [V_input gs y w hn]
      exact hxy _ hx
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < gs.length := by omega
    have hkj : k < (j : ℕ) := by omega
    let i : Fin gs.length := ⟨k, hk⟩
    have hi : i ≠ j := by
      intro heq
      exact (ne_of_lt hkj) (congrArg (fun z : Fin gs.length => (z : ℕ)) heq)
    rw [V_gate gs x k hk] at hx
    rw [V_gate gs y k hk]
    have hr (r : ℕ) : (if r < n + k then V gs x r else false) = true →
        (if r < n + k then V gs y r else false) = true := by
      intro hv
      by_cases h' : r < n + k
      · have hv' : V gs x r = true := by simpa [h'] using hv
        simpa [h'] using ih r h' (lt_trans h' hw) hv'
      · simp [h'] at hv
    have hmem : gs.get i ∈ gs := List.get_mem gs i
    rcases (hops _ hmem).1 with hand | hor | hnot
    · have hand' : gs[k].op = GateOp.and := by simpa [get_idx] using hand
      simp only [hand', GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · have hor' : gs[k].op = GateOp.or := by simpa [get_idx] using hor
      simp only [hor', GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hv⟩ := hx
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hv⟩
    · exact False.elim (hi (honly i hnot))

lemma offLine_le {n : ℕ} (L : Fin n → Finset (Fin n)) (i0 : Fin n)
    (x : Fin n → Bool) (hx : ∀ v, x v = true → v ∉ L i0) :
    ∀ v, x v = true → (fun u => decide (u ∉ L i0)) v = true := by
  intro v hv
  exact (decide_eq_true_iff).mpr (hx v hv)

lemma H_false {n : ℕ} (gs : List Gate) (j h : Fin gs.length)
    (L : Fin n → Finset (Fin n)) (i0 : Fin n)
    (hops : ∀ gt ∈ gs, (gt.op = GateOp.and ∨ gt.op = GateOp.or ∨ gt.op = GateOp.not) ∧
      gt.inputs.length ≤ 2)
    (honly : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (hlt : h < j)
    (hc : V gs (fun v => decide (v ∉ L i0)) (n + (h : ℕ)) = false)
    (z : Fin n → Bool) (hz : ∀ v, z v = true → v ∉ L i0) :
    V gs z (n + (h : ℕ)) = false := by
  by_contra hne
  have htrue : V gs z (n + (h : ℕ)) = true := by
    cases hv : V gs z (n + (h : ℕ)) with
    | true => rfl
    | false => exact False.elim (hne hv)
  have := monoEarly gs j hops honly z (fun v => decide (v ∉ L i0))
    (offLine_le L i0 z hz) (n + (h : ℕ)) (by omega) htrue
  rw [hc] at this
  exact Bool.false_ne_true this

lemma monoRegion {n : ℕ} (gs : List Gate) (j h : Fin gs.length)
    (L : Fin n → Finset (Fin n)) (i0 : Fin n)
    (hops : ∀ gt ∈ gs, (gt.op = GateOp.and ∨ gt.op = GateOp.or ∨ gt.op = GateOp.not) ∧
      gt.inputs.length ≤ 2)
    (honly : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (hop : (gs.get j).op = GateOp.not) (hlt : h < j)
    (hr : ∃ r : List ℕ, (gs.get j).inputs = (n + (h : ℕ)) :: r)
    (hc : V gs (fun v => decide (v ∉ L i0)) (n + (h : ℕ)) = false)
    (x y : Fin n → Bool)
    (hxoff : ∀ v, x v = true → v ∉ L i0) (hyoff : ∀ v, y v = true → v ∉ L i0)
    (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, V gs x w = true → V gs y w = true := by
  have hfalse := H_false gs j h L i0 hops honly hlt hc
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hearly : w < n + (j : ℕ)
    · exact monoEarly gs j hops honly x y hxy w hearly hx
    by_cases hmiss : n + gs.length ≤ w
    · rw [V_missing gs x w hmiss] at hx
      exact False.elim (Bool.false_ne_true hx)
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < gs.length := by omega
    by_cases hkj : k = (j : ℕ)
    · subst hkj
      rw [not_head gs j h hop hlt hr x] at hx
      rw [not_head gs j h hop hlt hr y]
      rw [hfalse x hxoff] at hx
      rw [hfalse y hyoff]
      exact hx
    · rw [V_gate gs y k hk]
      rw [V_gate gs x k hk] at hx
      let i : Fin gs.length := ⟨k, hk⟩
      have hi : i ≠ j := by
        intro heq
        exact hkj (congrArg (fun z : Fin gs.length => (z : ℕ)) heq)
      have hmem : gs.get i ∈ gs := List.get_mem gs i
      have hr (r : ℕ) : (if r < n + k then V gs x r else false) = true →
          (if r < n + k then V gs y r else false) = true := by
        intro hv
        by_cases h' : r < n + k
        · have hv' : V gs x r = true := by simpa [h'] using hv
          simpa [h'] using ih r h' hv'
        · simp [h'] at hv
      rcases (hops _ hmem).1 with hand | hor | hnot
      · have hand' : gs[k].op = GateOp.and := by simpa [get_idx] using hand
        simp only [hand', GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
        intro b hb
        obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
        exact hr r (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
      · have hor' : gs[k].op = GateOp.or := by simpa [get_idx] using hor
        simp only [hor', GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
        obtain ⟨b, hb, hv⟩ := hx
        obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
        exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hv⟩
      · exact False.elim (hi (honly i hnot))

end PEqualNP.Outside.L_meta_1645

theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _
  intro gates _ j h hops _ hop honly hlt hr _ ev hev hP0 hP1 hother hc
  have hc' : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v ∉ L i0)) (N + (h : ℕ)) = false := by
    rw [PEqualNP.Outside.L_meta_1645.V_eval, ← hev]
    exact hc
  have h0 : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v = p0)) (N + (h : ℕ)) = true := by
    rw [PEqualNP.Outside.L_meta_1645.V_eval, ← hev]; exact hP0
  have h1 : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v = p1)) (N + (h : ℕ)) = true := by
    rw [PEqualNP.Outside.L_meta_1645.V_eval, ← hev]; exact hP1
  have hJ0 : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v = p0)) (N + (j : ℕ)) = false := by
    rw [PEqualNP.Outside.L_meta_1645.not_head gates j h hop hlt hr, h0]; rfl
  have hJ1 : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v = p1)) (N + (j : ℕ)) = false := by
    rw [PEqualNP.Outside.L_meta_1645.not_head gates j h hop hlt hr, h1]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hxoff
    have hH : PEqualNP.Outside.L_meta_1645.V gates x (N + (h : ℕ)) = false :=
      PEqualNP.Outside.L_meta_1645.H_false gates j h L i0 hops honly hlt hc' x hxoff
    have hJ : PEqualNP.Outside.L_meta_1645.V gates x (N + (j : ℕ)) = true := by
      rw [PEqualNP.Outside.L_meta_1645.not_head gates j h hop hlt hr x, hH]
      rfl
    constructor
    · rw [hev, ← PEqualNP.Outside.L_meta_1645.V_eval]; exact hH
    · rw [hev, ← PEqualNP.Outside.L_meta_1645.V_eval]; exact hJ
  · intro w _ hwp0 hwp1
    have hH : ev (N + (h : ℕ)) (fun v => decide (v = w)) = false := hother w hwp0 hwp1
    have hHv : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v = w)) (N + (h : ℕ)) = false := by
      rw [PEqualNP.Outside.L_meta_1645.V_eval, ← hev]; exact hH
    have hJ : PEqualNP.Outside.L_meta_1645.V gates (fun v => decide (v = w)) (N + (j : ℕ)) = true := by
      rw [PEqualNP.Outside.L_meta_1645.not_head gates j h hop hlt hr, hHv]
      rfl
    constructor
    · exact hH
    · rw [hev, ← PEqualNP.Outside.L_meta_1645.V_eval]; exact hJ
  · rw [hev, ← PEqualNP.Outside.L_meta_1645.V_eval]; exact hJ0
  · rw [hev, ← PEqualNP.Outside.L_meta_1645.V_eval]; exact hJ1
  · intro w x y hxoff hyoff hxy hx
    have hx' : PEqualNP.Outside.L_meta_1645.V gates x w = true := by
      rw [PEqualNP.Outside.L_meta_1645.V_eval, ← hev]; exact hx
    have hy' : PEqualNP.Outside.L_meta_1645.V gates y w = true :=
      PEqualNP.Outside.L_meta_1645.monoRegion gates j h L i0 hops honly hop hlt hr hc' x y
        hxoff hyoff hxy w hx'
    rw [hev, ← PEqualNP.Outside.L_meta_1645.V_eval]; exact hy'
