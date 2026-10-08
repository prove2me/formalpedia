-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T21:04:18.224995+00:00
-- url     : https://prove2.me/theorems/e50526dc-0664-41df-ab1c-b260c3e1f923
-- title:
--   A canonical q-scale function is strictly positive in every unbounded-variation branch
-- statement:
--   If the canonical spectrally negative Lévy process has unbounded variation, then every q-scale function value is strictly positive at every positive capital level. The canonical dichotomy says unbounded variation means either a positive Gaussian coefficient or infinite first absolute moment of the small negative jumps. Strict positivity has been proved separately in those two branches, so this theorem is their exact composition.
-- source:
--   Compose Proved unbounded_variation_gaussian_or_infinite_small_jump_moment with scaleFunction_strict_pos_of_gaussian and scaleFunction_strict_pos_of_infinite_small_jump_moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    ∀ a : ℝ, 0 < a → 0 < W a := by sorry
