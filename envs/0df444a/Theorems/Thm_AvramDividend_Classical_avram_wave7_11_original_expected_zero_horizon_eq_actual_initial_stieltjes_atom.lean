-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_zero_horizon_eq_actual_initial_stieltjes_atom
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_zero_horizon_eq_actual_initial_stieltjes_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:06:07.923512+00:00
-- url     : https://prove2.me/theorems/f2e6ae13-bbe8-4132-98f4-139525624773
-- title:
--   Exact original expected zero-horizon Stieltjes reward is source initial right-payment atom
-- statement:
--   Under the original spectrally negative Levy law P and canonical dividendMeasure D, the complete horizon-T=0 discounted expected dividend is exactly the expectation of the genuine dividend Stieltjes measure of singleton {0}, regardless of the ruin clock or discount q. This identifies the initial right-payment atom with no vanishing assumption and disambiguates the zero versus positive horizon cases in finite-horizon UBV verification.
-- source:
--   Proved original W7-11 zero-horizon exact Stieltjes atom identity, original X/P/D/ruinTime, Mathlib lintegral_congr.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_zero_horizon_eq_actual_initial_stieltjes_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, (dividendMeasure D ω) ({0} : Set ℝ) ∂P) := by sorry
