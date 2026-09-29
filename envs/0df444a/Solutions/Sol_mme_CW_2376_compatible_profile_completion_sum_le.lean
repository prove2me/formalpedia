-- Prove2me | solution 1 for mme_CW_2376_compatible_profile_completion_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:15:54.466045+00:00
-- url     : https://prove2.me/submissions/23a49ff5-69ff-489b-97b2-715277f542c1

import Theorems.Thm_mme_CW_2376_target_factorial_profile_dominates

open MME BigOperators

set_option autoImplicit false

/-- Summing all compatible multinomial completion terms costs only the
number of feasible joint profiles once the target denominator dominates. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    (T : Finset ((Fin 3 → Fin 5) → ℕ)) (numerator : ℕ)
    (hT : ∀ a ∈ T,
      (∀ i : Fin 3, ∀ r : Fin 5,
        (∑ sigma ∈ cw2376TargetJointTypes,
          if sigma i = r then a sigma else 0) =
        ∑ sigma ∈ cw2376TargetJointTypes,
          if sigma i = r then cw2376ProfileMultiplicity m sigma else 0) ∧
      (∑ sigma ∈ cw2376TargetJointTypes, a sigma) =
        ∑ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma) :
    (∑ a ∈ T, numerator /
        ∏ sigma ∈ cw2376TargetJointTypes, (a sigma).factorial) ≤
      T.card * (numerator /
        ∏ sigma ∈ cw2376TargetJointTypes,
          (cw2376ProfileMultiplicity m sigma).factorial) := by
  have hterm : ∀ a ∈ T,
      numerator / (∏ sigma ∈ cw2376TargetJointTypes,
        (a sigma).factorial) ≤
      numerator / (∏ sigma ∈ cw2376TargetJointTypes,
        (cw2376ProfileMultiplicity m sigma).factorial) := by
    intro a ha
    have hden := mme_CW_2376_target_factorial_profile_dominates
      m hm a (hT a ha).1 (hT a ha).2
    apply Nat.div_le_div_left hden
    exact Finset.prod_pos fun sigma hsigma => Nat.factorial_pos _
  have hsum := Finset.sum_le_card_nsmul T
    (fun a => numerator /
      ∏ sigma ∈ cw2376TargetJointTypes, (a sigma).factorial)
    (numerator /
      ∏ sigma ∈ cw2376TargetJointTypes,
        (cw2376ProfileMultiplicity m sigma).factorial) hterm
  simpa [nsmul_eq_mul] using hsum
