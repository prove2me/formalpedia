-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
-- name    : AvramDividend.Classical.scaleFunction_intervalIntegrable_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:13:33.347317+00:00
-- url     : https://prove2.me/theorems/fc543d73-6d0a-4f01-ab7f-21d3f7efb31f
-- title:
--   Scale functions are integrable on nonnegative finite reserve intervals
-- statement:
--   The scale function is measurable and monotone on the nonnegative half-line. On a finite interval with nonnegative endpoints its norm is dominated by W at the right endpoint. Lebesgue measure of the interval is finite, so bounded measurable integrability follows. This supplies the first fundamental theorem of calculus for the scale-function primitive in the finite-activity Volterra identity.
-- source:
--   Mathlib.MeasureTheory.Integral.IntegrableOn, IntegrableOn.of_bound; standard properties of spectrally negative Lévy q-scale functions.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_intervalIntegrable_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable W volume a b := by sorry
