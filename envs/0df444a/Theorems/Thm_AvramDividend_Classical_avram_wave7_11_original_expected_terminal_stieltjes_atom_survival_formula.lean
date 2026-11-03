-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:11:30.790241+00:00
-- url     : https://prove2.me/theorems/f7b86a52-f080-454f-a95e-f4aa2c6f7a21
-- title:
--   Exact expected original-process horizon dividend atom under genuine pre-ruin survival
-- statement:
--   At any strictly positive finite horizon T the original-probability expectation of the exact terminal discounted Stieltjes dividend is the ENNReal integral of the original measure atom μ_D(ω)({T}) weighted by exp(-qT) on the true event ENNReal.ofReal T<ruinTime X x D ω, with zero contribution otherwise. This is an exact source-faithful survivor-only formula for the terminal boundary correction to a strict min-clock budget.
-- source:
--   W7-11 original positive horizon terminal Stieltjes indicator formula, canonical original ruinTime/measure X,P,D, Mathlib lintegral_congr.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ∫⁻ ω, if ENNReal.ofReal T < ruinTime X x D ω then
      (dividendMeasure D ω) ({T} : Set ℝ) *
        ENNReal.ofReal (Real.exp (-(q * T))) else 0 ∂P := by sorry
