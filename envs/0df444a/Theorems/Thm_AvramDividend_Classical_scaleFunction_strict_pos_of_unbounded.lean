-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:03:13.385037+00:00
-- url     : https://prove2.me/theorems/86c6d723-5739-4f5d-96b8-d35def9bfe4e
-- title:
--   A canonical q-scale function is strictly positive for unbounded-variation standing processes
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, every canonical q-scale function is strictly positive at positive arguments. The proof splits the canonical unbounded-variation dichotomy into a Gaussian branch and an infinite-small-jump-first-moment branch and applies the corresponding strict-positivity theorem.
-- source:
--   Compose Proved unbounded_variation_gaussian_or_infinite_small_jump_moment, Proved scaleFunction_strict_pos_of_gaussian, and scaleFunction_strict_pos_of_infinite_small_jump_moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    ∀ a : ℝ, 0 < a → 0 < W a := by sorry
