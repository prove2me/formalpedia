-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_self_convolution_positive
-- name    : AvramDividend.Classical.unbounded_scale_self_convolution_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:39:37.468083+00:00
-- url     : https://prove2.me/theorems/89e65416-225c-4aad-8eb1-c35ab5fc6516
-- title:
--   Strict positivity of unbounded-variation scale-function self-convolution
-- statement:
--   For any scale function of a spectrally negative Lévy process with unbounded variation, its causal self-convolution is strictly positive at each strictly positive reserve. This does not require a second discount parameter and supplies the positivity input for studying higher discount sensitivity.
-- source:
--   Direct application of the interval-integral positivity theorem, continuity and strict positivity of q-scale functions on the positive half-line.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_self_convolution_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ x : ℝ, 0 < x →
      0 < ∫ s in Ioc (0 : ℝ) x, W s * W (x - s) := by sorry
