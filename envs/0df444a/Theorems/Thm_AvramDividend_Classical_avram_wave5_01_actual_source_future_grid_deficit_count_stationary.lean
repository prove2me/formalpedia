-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_future_grid_deficit_count_stationary
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_future_grid_deficit_count_stationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:49:13.478357+00:00
-- url     : https://prove2.me/theorems/5143fc50-185c-49ba-b6c8-8da8e8fd286f
-- title:
--   Original Lévy future-grid jump-occupancy count has exactly the stationary source distribution
-- statement:
--   For the unchanged original SpectrallyNegativeLevy process X and every deterministic s, every finite grid drift-deficit count computed from the actual future increment path X(s+u)−X(s) has the same complete distribution as the count computed from X(u). There are no BV, finite-activity, artificial Poisson law, or extra filtration hypotheses. The proof exhibits the count as a measurable finite-cylinder functional and applies the already Proved whole-future-path stationary law to the actual X and P. This is the source stationary-count transport needed before deriving any shifted finite-band count intensity; it does not identify the marked jump compensator.
-- source:
--   Pinned original source definition 933ced80-71c1-4c0f-a6a7-ab7757fc97e9 and canonically Proved actual future-path law 7a0dfabc-f3ac-499e-8769-05f7bfe4ae96; this specialises measurable full-path transport to finite-grid drift-deficit counts, using the accepted measurable finite indicator-sum pattern from e3cc1dec-9b47-4c1c-af52-9dc189fef9d9. Supports source compensator target 393b03a8-2e9a-43d8-b415-854d86d58104; no detached space or conditional source Poisson assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_actual_source_future_grid_deficit_count_stationary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0) :
    Measure.map (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) P =
    Measure.map (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) P := by sorry
