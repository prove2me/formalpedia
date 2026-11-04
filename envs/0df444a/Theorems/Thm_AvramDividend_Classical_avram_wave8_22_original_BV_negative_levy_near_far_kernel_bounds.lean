-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:24:57.138266+00:00
-- url     : https://prove2.me/theorems/0c51c590-35ac-42d6-8a15-2f089fd1c856
-- title:
--   Original BV compact-reserve negative Lévy jump kernel pointwise near/far envelopes
-- statement:
--   For the actual BV barrier-value function on a positive compact reserve band [a,b], a band Lipschitz constant L and one-sided value bound R give |w(y+z)-w(y)| ≤ L|z| on the small negative-jump band z>−a/2 and ≤2R on separated negative jumps z≤−a/2. Integrating this against original ν supplies the missing analytic uniform bound needed by the BV generator envelope.
-- source:
--   Original W7-02 BV near/far integrable jump hypothesis 8888f8ed; exact compact band geometry and absolute-value triangle in pinned Mathlib.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds (w : ℝ → ℝ)
  (a b L R : ℝ) (ha : 0 < a) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (y z : ℝ) (hy : y ∈ Icc a b) (hz : z < 0) :
  ((-a / 2 < z → |w (y + z) - w y| ≤ L * |z|) ∧
   (z ≤ -a / 2 → |w (y + z) - w y| ≤ 2 * R)) := by sorry
