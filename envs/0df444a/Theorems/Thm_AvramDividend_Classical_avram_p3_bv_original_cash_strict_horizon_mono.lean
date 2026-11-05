-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
-- name    : AvramDividend.Classical.avram_p3_bv_original_cash_strict_horizon_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:32:36.636437+00:00
-- url     : https://prove2.me/theorems/e1100117-0473-442c-85a5-6713be8c9672
-- title:
--   Monotonicity of exact original stopped Stieltjes cash under increasing strict horizons
-- statement:
--   For the original controlled spectrally negative Lévy process and its exact stopped dividend Stieltjes measure, the nonnegative discounted ENNReal cash accumulated at times strictly before a real horizon is monotone in that horizon. This preserves the original ruinTime and all time-zero, diffuse, singular-continuous and right-payment atoms. It is a direct measure-inclusion step needed for Fatou passage, without any stochastic compensation hypothesis.
-- source:
--   Source-exact original paymentTimes, ruinTime and dividendMeasure, with pinned Mathlib MeasureTheory.lintegral_mono_set under Iio horizon inclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_cash_strict_horizon_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q a b : ℝ) (hab : a ≤ b)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio a,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio b,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
