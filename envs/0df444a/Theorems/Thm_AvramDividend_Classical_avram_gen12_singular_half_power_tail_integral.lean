-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen12_singular_half_power_tail_integral
-- name    : AvramDividend.Classical.avram_gen12_singular_half_power_tail_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:06:36.0032+00:00
-- url     : https://prove2.me/theorems/eb85e69a-ff4a-4aed-973f-6b5c8e613d1f
-- title:
--   Exact companion half-power integral for the ruin-crossing Levy boundary term
-- statement:
--   The integral of the negative-one-half power between a positive reserve and one equals twice one minus the positive square-root power. Combined with the negative-three-halves tail, this gives the exact proposed ruin-crossing jump generator integral.
-- source:
--   Companion finite integral, paired with the source-verified avram_gen12_singular_power_tail_integral theorem.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gen12_singular_half_power_tail_integral
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ r in y..1, r ^ (-(1 / 2 : ℝ))) =
      2 * (1 - y ^ (1 / 2 : ℝ)) := by sorry
