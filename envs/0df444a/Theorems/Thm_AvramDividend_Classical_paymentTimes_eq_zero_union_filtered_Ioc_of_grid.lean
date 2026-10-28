-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_zero_union_filtered_Ioc_of_grid
-- name    : AvramDividend.Classical.paymentTimes_eq_zero_union_filtered_Ioc_of_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:52:53.283762+00:00
-- url     : https://prove2.me/theorems/bd0b527a-8d44-4d1e-8b56-6aec7c954869
-- title:
--   Stop-time payment set is the initial atom and filtered positive Stieltjes prefixes
-- statement:
--   For any nonnegative countable time grid cofinal strictly before the stopping horizon, the exact strict pre-ruin payment set is the union of time zero and positive-time open-left closed-right prefixes whose grid endpoints remain strictly before ruin. Unlike a globally surviving-grid formulation, arbitrary deterministic rational grids are admitted by filtering their endpoints. The identity faithfully preserves the time-zero Stieltjes atom and the strict ruin endpoint, enabling extension from almost-sure weighted finite-horizon lemmas to the stopped payment reward.
-- source:
--   Prove2Me DividendStrategy.paymentTimes strict exit definition; Avram, Palmowski and Pistorius (2007), section 3.3.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.paymentTimes_eq_zero_union_filtered_Ioc_of_grid
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ) :
    paymentTimes σ =
      {(0 : ℝ)} ∪ ⋃ n : ℕ,
        {t : ℝ | 0 < t ∧ t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ} := by sorry
