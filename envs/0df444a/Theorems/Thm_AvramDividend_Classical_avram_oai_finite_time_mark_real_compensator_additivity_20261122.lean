-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_finite_time_mark_real_compensator_additivity_20261122
-- name    : AvramDividend.Classical.avram_oai_finite_time_mark_real_compensator_additivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:55:50.690427+00:00
-- url     : https://prove2.me/theorems/c61595e9-5db8-4578-ae64-7ff1db7300a9
-- title:
--   Exact real-valued finite-time Lévy mark compensator rate additivity on adjacent intervals
-- statement:
--   For any nonnegative real times s≤t and any possibly infinite extended nonnegative mark intensity m, prove ((t:ENNReal)*m).toReal = ((s:ENNReal)*m).toReal + (((t−s:NNReal):ENNReal)*m).toReal. This deterministic identity is true even at m=∞ by the ENNReal-toReal convention and is the exact compensator arithmetic needed to turn original physical finite mark real-count interval additivity into compensated mark-increment additivity. It uses pinned ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_sub and ring.

import Mathlib
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_finite_time_mark_real_compensator_additivity_20261122
    (s t : ℝ≥0) (hst : s ≤ t) (m : ℝ≥0∞) :
    ((t : ℝ≥0∞) * m).toReal =
      ((s : ℝ≥0∞) * m).toReal +
        (((t - s : ℝ≥0) : ℝ≥0∞) * m).toReal := by sorry
