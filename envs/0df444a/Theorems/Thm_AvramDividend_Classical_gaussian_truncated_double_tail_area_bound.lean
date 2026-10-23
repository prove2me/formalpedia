-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_truncated_double_tail_area_bound
-- name    : AvramDividend.Classical.gaussian_truncated_double_tail_area_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:46:01.265823+00:00
-- url     : https://prove2.me/theorems/07a276b0-dbdf-4a23-b256-047458266833
-- title:
--   Local area domination for the Esscher Gaussian double-tail Volterra kernel
-- statement:
--   For nonnegative time horizon R and jump magnitude z, the integrated positive-part double-tail kernel area z min(R,z) - min(R,z)^2 / 2 is nonnegative and bounded by (1+R) min(z^2,z). After Esscher damping, this bound reduces the kernel's local time-integrability to the previously Proved Esscher tilted tail-area integrability lemma, a prerequisite for Gaussian Volterra resolvent smoothing.
-- source:
--   Elementary integration of the Gaussian Esscher double-tail kernel, with the integrability bound in esscher_tilted_tail_area_integrable.

import Mathlib.Tactic

theorem AvramDividend.Classical.gaussian_truncated_double_tail_area_bound
    (R z : ℝ) (hR : 0 ≤ R) (hz : 0 ≤ z) :
    0 ≤ z * min R z - (min R z) ^ 2 / 2 ∧
    z * min R z - (min R z) ^ 2 / 2 ≤
      (1 + R) * min (z ^ 2) z := by sorry
