-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_original_supremum_scale_clock_moment
-- name    : AvramDividend.Classical.avram_ws01b_original_supremum_scale_clock_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:03:47.690177+00:00
-- url     : https://prove2.me/theorems/f3b5cbcc-2f16-45f5-bcb3-c9127a68d7a3
-- title:
--   Exact original exponential-clock supremum q-scale reward moment
-- statement:
--   For the true original spectrally negative Lévy process and independent Exp(R) clock with positive root φ, the nonnegative extended expected q-scale function of the actual running supremum is φ/(R-q), for R>q, including the BV nonzero scale origin. This is a genuine source-law moment needed for the zero-cap killed resolvent, obtained from the accepted actual supremum exponential law and defining scale-function Laplace transform.
-- source:
--   Actual original Exp(R) supremum law 8ecbee20, source scale-positive ENNReal Laplace 7654d06e, density definition of Mathlib expMeasure and Measurable W. Integral is nonnegative extended to avoid unproved uniform integrability; BV zero origin is covered by Lebesgue-null singleton at zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_original_supremum_scale_clock_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q R φ : ℝ) (hR : 0 < R) (hqR : q < R)
    (hφ : 0 < φ) (hroot : X.ψ φ = R)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (W (runningSup X z.2.toNNReal z.1))
      ∂(P.prod (expMeasure R))) =
    ENNReal.ofReal (φ / (R - q)) := by sorry
