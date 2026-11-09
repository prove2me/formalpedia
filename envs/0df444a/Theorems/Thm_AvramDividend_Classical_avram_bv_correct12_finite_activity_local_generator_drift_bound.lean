-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_local_generator_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T20:08:46.060201+00:00
-- url     : https://prove2.me/theorems/e6d7e520-a7c4-4740-8d26-629b560278c5
-- title:
--   Original finite-activity BV generator bound using only nonnegative negative-jump destinations
-- statement:
--   For the original bounded-variation spectrally negative process with finite negative jump rate, the drift-derivative term is at most the discount-plus-rate times the value whenever the genuine generator satisfies its HJB upper and the candidate is nonnegative only at destinations of negative jumps from the current reserve. Global nonnegativity, which fails for general uncapped extensions, is unnecessary.
-- source:
--   Root-connected BV-CORRECT12 origin-boundary input to 51b72610. Refines Proved fa9b7e98 by restricting candidate nonnegativity to actual negative-jump destinations. Uses Proved original-process physical BV generator formula and finite-activity restricted-measure comparison.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_local_generator_drift_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y)
    (hHJB : X.generator w y - q * w y ≤ 0)
    (hLocal : ∀ z : ℝ, z < 0 → 0 ≤ w (y + z)) :
    X.drift * deriv w y ≤
      (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by sorry
