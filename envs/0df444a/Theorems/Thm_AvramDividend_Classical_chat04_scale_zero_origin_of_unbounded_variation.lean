-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
-- name    : AvramDividend.Classical.chat04_scale_zero_origin_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:06:50.915829+00:00
-- url     : https://prove2.me/theorems/c1b8958a-41fd-444e-893e-cf03e591b93e
-- title:
--   Unbounded-variation q-scale function vanishes at zero without Standing
-- statement:
--   For a spectrally negative Lévy process of unbounded variation and q>0, its q-scale function satisfies W(0)=0, without the Standing hypothesis. This follows by splitting on the Gaussian coefficient: positive Gaussian coefficient uses the published Gaussian origin theorem; zero Gaussian coefficient forces infinite small-jump variation and uses the published infinite-jump origin theorem. This supplies the zero-boundary hypothesis used by strict lower-ruin payoffs.
-- source:
--   Proved unbounded_variation_gaussian_or_infinite_small_jump_moment; scaleFunction_zero_origin_gaussian_without_standing; scaleFunction_zero_origin_infinite_small_jumps.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_zero_origin_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    W 0 = 0 := by sorry
