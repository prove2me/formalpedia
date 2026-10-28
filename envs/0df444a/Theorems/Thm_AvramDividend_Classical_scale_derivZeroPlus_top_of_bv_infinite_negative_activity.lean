-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_derivZeroPlus_top_of_bv_infinite_negative_activity
-- name    : AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:07:58.965617+00:00
-- url     : https://prove2.me/theorems/0893ca6f-97f2-4965-b369-8e65116e9249
-- title:
--   Infinite negative activity forces infinite right scale slope in bounded variation
-- statement:
--   In the bounded-variation spectrally negative Lévy case, W(0)=1/d and its zero-right derivative is (q+lambda)/d² where lambda is the negative-jump intensity, interpreted as +infinity when lambda is infinite. Prove the infinite extended right derivative from the defining Laplace transform without extra smoothness assumptions.
-- source:
--   Avram, Palmowski and Pistorius (2007), equations (3.12)-(3.13), https://arxiv.org/pdf/math/0702893. Proved deterministic bridge derivZeroPlus_eq_top_of_right_tendsto_atTop supports the final analytic step.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    derivZeroPlus W = ⊤ := by sorry
