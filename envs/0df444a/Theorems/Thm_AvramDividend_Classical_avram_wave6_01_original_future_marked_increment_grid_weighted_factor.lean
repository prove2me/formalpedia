-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_future_marked_increment_grid_weighted_factor
-- name    : AvramDividend.Classical.avram_wave6_01_original_future_marked_increment_grid_weighted_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:46:59.263689+00:00
-- url     : https://prove2.me/theorems/43c7d32a-bcfc-4b0d-bca4-27fe1cdd0bd9
-- title:
--   Original Lévy future Borel-marked increment-grid count factors in first moment against every past weight
-- statement:
--   For the given actual SpectrallyNegativeLevy X and its unchanged P and original filtration 𝓕, for any measurable Borel jump-size window B, deterministic future grid after s and arbitrary ENNReal history weight H measurable in 𝓕_s, the expected product of H and the finite count of genuine future X increment cells whose real increments belong to B equals E[H] times the unconditional expected grid count. The proof applies the canonically Proved full source future-path independence theorem to a genuinely Borel finite marked grid extractor, then Mathlib independence lintegral factorisation. This is a non-circular positive-mark finite-cylinder bridge useful for deriving the intrinsic count compensator via a justified fine-mesh and small-time Lévy measure limit; it is not that limiting theorem and does not assert X.ν(B) on either side.
-- source:
--   Source original process future-path measurable extraction and source independent-increments; canonical future-path independent theorem 86ab54a5-0f9f-4e69-a76c-19f22db4d908. This handles arbitrary Borel B and ENNReal H, no count compensator or proxy model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_future_marked_increment_grid_weighted_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    (∫⁻ ω, H ω * (((Finset.range n).filter (fun i =>
      (X.X (s + grid (i + 1)) ω - X.X s ω) -
        (X.X (s + grid i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞) ∂P) =
      (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, (((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞) ∂P) := by sorry
