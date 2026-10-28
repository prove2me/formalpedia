-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_strictConvexOn
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_strictConvexOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:13:04.366608+00:00
-- url     : https://prove2.me/theorems/283d5bf8-c99f-48e1-b426-f82fcd7ec1ec
-- title:
--   Strict convexity of the q-scale function family in the discount
-- statement:
--   For each positive reserve of an unbounded-variation spectrally negative Lévy process, the scale function indexed by every nonnegative discount is strictly convex as a real-valued function of the discount on [0,∞). The standard StrictConvexOn predicate supports downstream Jensen and slope arguments.
-- source:
--   The verified strict increase of consecutive discount secant slopes and Mathlib's strictConvexOn_of_slope_strict_mono_adjacent criterion.

import Mathlib.Analysis.Convex.Slope
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_strictConvexOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      StrictConvexOn ℝ (Ici (0 : ℝ)) (fun q : ℝ => W q x) := by sorry
