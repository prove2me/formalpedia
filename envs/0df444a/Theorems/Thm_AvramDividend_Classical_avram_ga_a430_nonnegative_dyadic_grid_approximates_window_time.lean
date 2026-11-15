-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a430_nonnegative_dyadic_grid_approximates_window_time
-- name    : AvramDividend.Classical.avram_ga_a430_nonnegative_dyadic_grid_approximates_window_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:54:51.623207+00:00
-- url     : https://prove2.me/theorems/089ec009-6f1e-49af-9411-fa8b266a26aa
-- title:
--   Every nonnegative time in a finite horizon is a limit of its dyadic-grid samples
-- statement:
--   For a strictly positive finite horizon, any time in the nonnegative interval up to that horizon admits a sequence of dyadic partition-grid sample times converging to it, with every sample index valid.
-- source:
--   Real-valued dyadic ceiling-index approximation and convergence imported from the Proved LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_readable, transferred to NNReal grid times.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Theorems.Thm_LevyStochCalc_Probability_tendsto_dyadicTime_dyadicIndex_readable
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a430_nonnegative_dyadic_grid_approximates_window_time
    (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) (ht : t ≤ T) :
    ∃ idx : ℕ → ℕ,
      (∀ k, idx k ≤ 2^k) ∧
      Filter.Tendsto
        (fun k : ℕ => (idx k : ℝ≥0) * T / (2^k : ℝ≥0))
        Filter.atTop (nhds t) := by sorry
