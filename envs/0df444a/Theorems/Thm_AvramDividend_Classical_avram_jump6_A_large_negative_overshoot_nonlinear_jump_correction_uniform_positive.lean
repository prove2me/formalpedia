-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_overshoot_nonlinear_jump_correction_uniform_positive
-- name    : AvramDividend.Classical.avram_jump6_A_large_negative_overshoot_nonlinear_jump_correction_uniform_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:08:16.686224+00:00
-- url     : https://prove2.me/theorems/9746d582-6bf1-48fd-ad7c-9279417ab1fa
-- title:
--   Every sufficiently large negative ruin-overshooting mark has a uniformly positive nonlinear jump correction
-- statement:
--   For the original spectrally negative Lévy dividend HJB candidate w(u)=0 on negative reserves and 1+u+u² on nonnegative reserves, any reserve 0≤y≤1/5 and any negative jump z≤−2 necessarily overshoots ruin. The genuine nonlinear marked-value jump compensation remainder w(y+z)−w(y)−z is at least 19/25, strictly positive uniformly over all such marked jumps, including the original size-two negative Poisson model. This extends the accepted single mark source 6814c123 to the full large-negative-mark tail and identifies a necessary positive term absent from the deprecated unit-coefficient fullmark martingale ledger.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_large_negative_overshoot_nonlinear_jump_correction_uniform_positive
    (y z : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5)
    (hz : z ≤ -2) :
    (if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
      (if y < 0 then 0 else 1 + y + y ^ 2) - z ≥ 19 / 25 := by sorry
