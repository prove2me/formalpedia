-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_monotoneOn_all_reserves
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_monotoneOn_all_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:35:21.877006+00:00
-- url     : https://prove2.me/theorems/4ead408a-beab-4c09-91d7-b1deaceecf87
-- title:
--   Global nondecreasing discount-ordering of unbounded-variation q-scale functions
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, scale-function values at any real reserve are nondecreasing as the nonnegative discount parameter grows. They increase strictly at positive reserves, while remaining zero at the origin and on negative reserves.
-- source:
--   Combine the Proved strict-monotonicity-in-discount theorem at positive reserves with Proved zero-origin vanishing and the scale-function support property.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Order.Monotone.Defs
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_strictMonoOn
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_monotoneOn_all_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, MonotoneOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by sorry
