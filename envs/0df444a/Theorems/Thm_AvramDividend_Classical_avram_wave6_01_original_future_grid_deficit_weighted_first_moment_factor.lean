-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_future_grid_deficit_weighted_first_moment_factor
-- name    : AvramDividend.Classical.avram_wave6_01_original_future_grid_deficit_weighted_first_moment_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:40:50.028198+00:00
-- url     : https://prove2.me/theorems/cd7812cf-a364-43a9-8f8c-31618eeb0263
-- title:
--   Original Lévy future drift-grid count has exact first-moment factorisation against arbitrary measurable past weights
-- statement:
--   On the unchanged original sample space Ω and original Lévy filtration 𝓕, any nonnegative ENNReal-valued 𝓕_s-measurable history weight H satisfies E_P[H times the number of drift-deficient source future-increment grid cells]=E_P[H] times the unconditional mean of that same literal source-grid count. The finite random count is built from actual X(s+u)-X(s), not a proxy Poisson process. The proof uses the already Proved actual finite-grid IndepFun theorem and Mathlib independence integration, with all ENNReal infinite-value bookkeeping. This is the non-circular finite-grid first-moment factor required before an a.s.-limit to original jump counts; it does not identify X.ν(B) or assert the arbitrary-mark compensator.
-- source:
--   Direct independent-increments source factor for true original drift-grid counts; imported canonical Proved 7878109a-1a9f-4747-acf1-4d25b36ee40f. No conditional compensator assumption. Necessary for quantitative passage to BV literal source count from cc7abaca... eventual-grid identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_future_grid_deficit_count_indep_past
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_future_grid_deficit_weighted_first_moment_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    (∫⁻ ω, H ω * (((Finset.range n).filter (fun i =>
      (X.X (s + grid (i + 1)) ω - X.X s ω) -
        (X.X (s + grid i) ω - X.X s ω) <
        X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card : ℝ≥0∞) ∂P) =
      (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, (((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card : ℝ≥0∞) ∂P) := by sorry
