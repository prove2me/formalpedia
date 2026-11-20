-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_discounted_original_first_negative_size2_mark_nonlinear_compensation_positive_gap
-- name    : AvramDividend.Classical.avram_jump6_A_discounted_original_first_negative_size2_mark_nonlinear_compensation_positive_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:02:46.273196+00:00
-- url     : https://prove2.me/theorems/a1700d55-798e-4c60-b543-128d8c5b33c8
-- title:
--   Strictly positive discounted nonlinear Lévy jump correction at the actual size-two ruin mark
-- statement:
--   At any pre-jump reserve 0≤y≤1/5 and any discount clock τ, the true nonlinear marked generator increment w(y−2)−w(y), where w(z)=0 on negative reserves and w(z)=1+z+z² on nonnegative reserves, differs from the raw linear size-two Poisson mark −2 by at least 19/25. After multiplication by the strictly positive exponential discount e^(−qτ), this missing nonlinear correction remains strictly positive, with an explicit lower bound (19/25)e^(−qτ). This quantifies the omitted term in the deprecated original unit-fullmark signed physical Itô-Meyer cash source and identifies the correction needed for a sound full nonlinear compensated jump martingale.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
set_option autoImplicit false
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_discounted_original_first_negative_size2_mark_nonlinear_compensation_positive_gap
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5)
    (τ q : ℝ) :
    (19 / 25 : ℝ) * Real.exp (-(q * τ)) ≤
      Real.exp (-(q * τ)) *
        ((if y - 2 < 0 then 0
          else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
           (-2 : ℝ)) ∧
    0 < Real.exp (-(q * τ)) *
        ((if y - 2 < 0 then 0
          else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
           (-2 : ℝ)) := by sorry
