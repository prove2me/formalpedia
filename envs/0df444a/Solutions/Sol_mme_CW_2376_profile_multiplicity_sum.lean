-- Prove2me | solution 1 for mme_CW_2376_profile_multiplicity_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:44:31.945603+00:00
-- url     : https://prove2.me/submissions/e96dc7c4-d0f0-46f5-b684-43517701443b

import Definitions.Def_mme_CW_2376_joint_profile_table
import Theorems.Thm_mme_CW_2376_integer_profile

open MME BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem solution (m : ℕ) :
    (∑ σ : Fin 3 → Fin 5, cw2376ProfileMultiplicity m σ) =
      cw2376ProfileLength m := by
  classical
  have hsCard : cw2376ScalarTypes.card = 3 := by decide
  have hrCard : cw2376RectTypes.card = 6 := by decide
  have hcCard : cw2376CentralTypes.card = 3 := by decide
  have hdCard : cw2376CoupledTypes.card = 3 := by decide
  have hsr : Disjoint cw2376ScalarTypes cw2376RectTypes := by decide
  have hsc : Disjoint cw2376ScalarTypes cw2376CentralTypes := by decide
  have hsd : Disjoint cw2376ScalarTypes cw2376CoupledTypes := by decide
  have hrc : Disjoint cw2376RectTypes cw2376CentralTypes := by decide
  have hrd : Disjoint cw2376RectTypes cw2376CoupledTypes := by decide
  have hcd : Disjoint cw2376CentralTypes cw2376CoupledTypes := by decide
  have hpoint : ∀ σ : Fin 3 → Fin 5,
      cw2376ProfileMultiplicity m σ =
        (if σ ∈ cw2376ScalarTypes then 699 * m else 0) +
        (if σ ∈ cw2376RectTypes then 37518 * m else 0) +
        (if σ ∈ cw2376CentralTypes then 307638 * m else 0) +
        (if σ ∈ cw2376CoupledTypes then 616627 * m else 0) := by
    intro σ
    by_cases hs : σ ∈ cw2376ScalarTypes
    · have hr : σ ∉ cw2376RectTypes := fun h =>
        Finset.disjoint_left.mp hsr hs h
      have hc : σ ∉ cw2376CentralTypes := fun h =>
        Finset.disjoint_left.mp hsc hs h
      have hd : σ ∉ cw2376CoupledTypes := fun h =>
        Finset.disjoint_left.mp hsd hs h
      simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
    by_cases hr : σ ∈ cw2376RectTypes
    · have hc : σ ∉ cw2376CentralTypes := fun h =>
        Finset.disjoint_left.mp hrc hr h
      have hd : σ ∉ cw2376CoupledTypes := fun h =>
        Finset.disjoint_left.mp hrd hr h
      simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
    by_cases hc : σ ∈ cw2376CentralTypes
    · have hd : σ ∉ cw2376CoupledTypes := fun h =>
        Finset.disjoint_left.mp hcd hc h
      simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
    by_cases hd : σ ∈ cw2376CoupledTypes
    · simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
    · simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
  have hindicator (s : Finset (Fin 3 → Fin 5)) (c : ℕ) :
      (∑ σ : Fin 3 → Fin 5, if σ ∈ s then c else 0) = s.card * c := by
    change (∑ σ ∈ Finset.univ, if σ ∈ s then c else 0) = _
    rw [Finset.sum_ite]
    simp [Finset.filter_mem_eq_inter]
  rw [Finset.sum_congr rfl (fun σ _ => hpoint σ),
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib,
    hindicator, hindicator, hindicator, hindicator,
    hsCard, hrCard, hcCard, hdCard]
  unfold cw2376ProfileLength
  omega
