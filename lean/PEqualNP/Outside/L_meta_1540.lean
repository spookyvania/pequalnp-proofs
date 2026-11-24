import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1540 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)) (w : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = q → w ∈ L i0 → w ∉ T0 →
    (∀ x : Fin N → Bool, ((∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) ∧ ¬ ∃ v ∈ T0, x v = true) ↔
      (x = (fun v : Fin N => decide (v ∉ L i0)) ∨ x = (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)))) ∧
    (∀ s : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, (fun v : Fin N => decide (v ∉ L s)) v = false → v ∈ L s) ∧ (s ≠ i0 → ∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true)) ∧
    (∀ x : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) ↔ ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true)) ∧
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, y v = false → v ∈ L s)) := by
  intro q N L i0 T0 w hq _ hline hinter _ hTsub hTcard hwmem hwout
  have hTeq : T0 = (L i0).erase w := by
    have hsub : T0 ⊆ (L i0).erase w := by
      intro v hv
      exact Finset.mem_erase.mpr ⟨fun hvw => hwout (hvw ▸ hv), hTsub hv⟩
    have hcard : ((L i0).erase w).card = T0.card := by
      rw [Finset.card_erase_of_mem hwmem, hline i0, hTcard]
      omega
    exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
  have onlyLine (s : Fin N) (hcontain : T0 ⊆ L s) : s = i0 := by
    by_contra hne
    have hle : T0.card ≤ (L s ∩ L i0).card :=
      Finset.card_le_card (fun v hv => Finset.mem_inter.mpr ⟨hcontain hv, hTsub hv⟩)
    rw [hinter s i0 hne, hTcard] at hle
    omega
  have falseOnT {x : Fin N → Bool} (hno : ¬ ∃ v ∈ T0, x v = true) {v : Fin N}
      (hv : v ∈ T0) : x v = false := by
    cases hvx : x v with
    | false => rfl
    | true => exact False.elim (hno ⟨v, hv, hvx⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨⟨s, hs⟩, hno⟩
      have hs0 : s = i0 := onlyLine s (fun v hv => hs v (falseOnT hno hv))
      have hfalse : ∀ v, x v = false → v ∈ L i0 := fun v hv => by simpa [hs0] using hs v hv
      by_cases hxw : x w = true
      · right
        funext v
        cases hvx : x v with
        | false =>
          have hvL : v ∈ L i0 := hfalse v hvx
          have hvw : v ≠ w := by
            intro hvw
            rw [hvw] at hvx
            exact Bool.false_ne_true (hvx.symm.trans hxw)
          have hvT : v ∈ T0 := by
            rw [hTeq]
            exact Finset.mem_erase.mpr ⟨hvw, hvL⟩
          have : ¬ (v ∉ L i0 ∨ v = w) := by
            exact fun h => h.elim (fun hni => hni hvL) hvw
          exact (decide_eq_false_iff_not.mpr this).symm
        | true =>
          have hdis : v ∉ L i0 ∨ v = w := by
            by_cases hvL : v ∈ L i0
            · right
              by_contra hvw
              have hvT : v ∈ T0 := by
                rw [hTeq]
                exact Finset.mem_erase.mpr ⟨hvw, hvL⟩
              exact Bool.false_ne_true ((falseOnT hno hvT).symm.trans hvx)
            · left
              exact hvL
          exact (decide_eq_true_iff.mpr hdis).symm
      · left
        have hxwf : x w = false := by
          cases hx : x w with
          | false => rfl
          | true => exact False.elim (hxw hx)
        funext v
        cases hvx : x v with
        | false =>
          have hvL : v ∈ L i0 := hfalse v hvx
          exact (decide_eq_false_iff_not.mpr (fun hni => hni hvL)).symm
        | true =>
          have hvout : v ∉ L i0 := by
            intro hvL
            have hvw : v ≠ w := by
              intro hvw
              rw [hvw] at hvx
              exact Bool.false_ne_true (hxwf.symm.trans hvx)
            have hvT : v ∈ T0 := by
              rw [hTeq]
              exact Finset.mem_erase.mpr ⟨hvw, hvL⟩
            exact Bool.false_ne_true ((falseOnT hno hvT).symm.trans hvx)
          exact (decide_eq_true_iff.mpr hvout).symm
    · rintro (hx | hx)
      · refine ⟨⟨i0, ?_⟩, ?_⟩
        · intro v hv
          have : decide (v ∉ L i0) = false := by simpa [hx] using hv
          simpa using of_decide_eq_false this
        · rintro ⟨v, hv, hvx⟩
          have : v ∉ L i0 := of_decide_eq_true (by simpa [hx] using hvx)
          exact this (hTsub hv)
      · refine ⟨⟨i0, ?_⟩, ?_⟩
        · intro v hv
          have hnot : ¬ (v ∉ L i0 ∨ v = w) :=
            of_decide_eq_false (by simpa [hx] using hv)
          simpa using (not_or.mp hnot).1
        · rintro ⟨v, hv, hvx⟩
          have hor : v ∉ L i0 ∨ v = w :=
            of_decide_eq_true (by simpa [hx] using hvx)
          rcases hor with hvout | hvw
          · exact hvout (hTsub hv)
          · exact hwout (hvw ▸ hv)
  · intro s
    refine ⟨Or.inr ⟨s, ?_⟩, ?_⟩
    · intro v hv
      simpa using of_decide_eq_false hv
    · intro hs
      by_contra hall
      push Not at hall
      have hsub : T0 ⊆ L s := by
        intro v hv
        have hne : decide (v ∉ L s) ≠ true := hall v hv
        cases h : decide (v ∉ L s) with
        | false => simpa using of_decide_eq_false h
        | true => exact False.elim (hne h)
      have hle : T0.card ≤ 1 := by
        simpa [hinter s i0 hs] using
          Finset.card_le_card fun v hv => Finset.mem_inter.mpr ⟨hsub hv, hTsub hv⟩
      omega
  · intro x
    constructor
    · rintro (hhit | ⟨s, hs⟩)
      · exact Or.inl hhit
      · by_cases hhit : ∃ v ∈ T0, x v = true
        · exact Or.inl hhit
        · right
          have hs0 : s = i0 := onlyLine s (fun v hv => hs v (falseOnT hhit hv))
          intro v hvout
          cases hvx : x v with
          | true => rfl
          | false => exact False.elim (hvout (by simpa [hs0] using hs v hvx))
    · rintro (hhit | hall)
      · exact Or.inl hhit
      · refine Or.inr ⟨i0, ?_⟩
        intro v hv
        by_contra hvout
        exact Bool.false_ne_true (hv.symm.trans (hall v hvout))
  · intro x y hx hxy
    rcases hx with hhit | ⟨s, hs⟩
    · obtain ⟨v, hv, hvx⟩ := hhit
      exact Or.inl ⟨v, hv, hxy v hvx⟩
    · refine Or.inr ⟨s, ?_⟩
      intro v hv
      cases hxv : x v with
      | false => exact hs v hxv
      | true => exact False.elim (Bool.false_ne_true (hv.symm.trans (hxy v hxv)))
