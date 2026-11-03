-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_countable_future_marked_grid_sup_past_factor
-- name    : AvramDividend.Classical.avram_wave7_01_original_countable_future_marked_grid_sup_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:41:06.961197+00:00
-- url     : https://prove2.me/theorems/c70afb03-9168-497f-8bb4-5b0cc851afb4
-- title:
--   Original Lévy past weights factor against the supremum of countably many future Borel-marked grids
-- statement:
--   On the exact original Ω,P,X,𝓕, any past-measurable nonnegative H factors in expectation from the supremum over a countable family of finite Borel-marked future-increment grid counts. The supremum is a genuinely product-measurable extended-real functional of the same shifted future path; no limiting jump-count identification, ν-rate, or finite activity is assumed. The result supplies the countable-grid limit independence component of the compensator construction.
-- source:
--   Proved exact original future path independence 86ab54a5, measurable finite grid mark tests, Mathlib measurable_iSup and ENNReal independence lintegral factorisation; extends Proved 43c7d32a count finite grids.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_original_countable_future_marked_grid_sup_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0) :
    (∫⁻ ω, H ω * (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
      (X.X (s + grid k (i + 1)) ω - X.X s ω) -
      (X.X (s + grid k i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞)) ∂P) =
      (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
      (X.X (s + grid k (i + 1)) ω - X.X s ω) -
      (X.X (s + grid k i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞)) ∂P) := by sorry
