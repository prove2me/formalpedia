-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_strict_clipped_times_subset_natural_closed
-- name    : AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_times_subset_natural_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:28:28.113379+00:00
-- url     : https://prove2.me/theorems/e2b750c0-a55e-4b57-9f16-aade65f4e20b
-- title:
--   Strict ruin/natural-time clipped payment times lie inside the matching closed physical ruin clock
-- statement:
--   For every original extended nonnegative ruin clock σ and natural horizon n, each payment time strictly before min(σ,n), including the exact time-zero atom, belongs to the original payment times before σ and to the closed real time horizon at (min(σ,n)).toNNReal. This is the exact set inclusion needed to transport bounded original-process stopped cash budgets without adding a horizon atom.
-- source:
--   Source-faithful SWEEP16 reduction for corrected UBV 429e17ca, original stopped-clock 750ad13b and the previously Proved natural localised Ito cash budget 3b8e6210. paymentTimes has literal source definition 0≤t ∧ (t=0 ∨ ENNReal.ofReal t<σ). Pinned Mathlib ENNReal.ofReal_lt_iff_lt_toReal supports real-horizon comparison. No physical-process change or L1 martingale assumption is introduced.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_times_subset_natural_closed
    (σ : ℝ≥0∞) (n : ℕ) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆
      paymentTimes σ ∩ Set.Iic (((min σ (n : ℝ≥0∞)).toNNReal : ℝ)) := by sorry
