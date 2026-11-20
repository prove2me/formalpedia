-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_uniform_discounted_early_ruin_mark_missing_nonlinear_jump_budget
-- name    : AvramDividend.Classical.avram_jump6_A_uniform_discounted_early_ruin_mark_missing_nonlinear_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:03:37.812308+00:00
-- url     : https://prove2.me/theorems/3cb2dece-c862-406d-967c-0782b74e3ff7
-- title:
--   Uniform positive discounted missing nonlinear ruin-mark correction for every early size-two negative jump
-- statement:
--   For every genuine negative size-two Poisson ruin-causing jump from original reserve y∈[0,1/5], for a strictly nonnegative discount rate q and any early firstmark stopped time σ∈[0,1/500], the nonlinear value increment w(y−2)−w(y) differs from the raw unit-coefficient mark −2 by a positive amount. The discounted missing jump correction is bounded below by the explicit deterministic constant (19/25)exp(−q/500), strictly positive independently of σ and y. Thus the deprecated physical Jfull signed Itô source omission creates a uniform positive deficit on the original Brownian/Poisson tube event and cannot be concealed in mesh errors tending to zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
set_option autoImplicit false
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_uniform_discounted_early_ruin_mark_missing_nonlinear_jump_budget
    (y σ q : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5)
    (hσ : 0 ≤ σ) (hσearly : σ ≤ 1 / 500)
    (hq : 0 ≤ q) :
    (19 / 25 : ℝ) * Real.exp (-(q / 500)) ≤
      Real.exp (-(q * σ)) *
        ((if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
          (-2 : ℝ)) ∧
    0 < Real.exp (-(q * σ)) *
        ((if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) -
          (-2 : ℝ)) := by sorry
