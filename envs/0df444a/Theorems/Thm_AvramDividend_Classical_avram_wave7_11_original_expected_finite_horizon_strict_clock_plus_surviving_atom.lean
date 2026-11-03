-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_finite_horizon_strict_clock_plus_surviving_atom
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_finite_horizon_strict_clock_plus_surviving_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:18:18.057135+00:00
-- url     : https://prove2.me/theorems/d0e9e0f1-0987-43da-91ad-740fac816a80
-- title:
--   Exact expected finite-horizon Lévy dividend cash equals strict min-clock cash plus surviving terminal atom
-- statement:
--   For the exact original spectrally negative Levy process X under P, admissible dividend strategy D and source ruinTime, at every strictly positive real T the complete discounted expected source Stieltjes dividend payout equals the expected strict ruin clock min(ruinTime,T) payout plus exactly the expected discounted original dividend-measure atom at T on the event the original ruin clock strictly exceeds T. This is the full exact finite-horizon boundary correction required when the strict clock is truncated at the horizon itself; it never assumes vanishing jumps or continuous dividends.
-- source:
--   W7-11 original expected exact positive-horizon payment set decomposition, W7-11 expected positive terminal survival indicator formula, original source Avram spectrally negative Levy P/X/D.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_finite_horizon_strict_clock_plus_surviving_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (∫⁻ ω, if ENNReal.ofReal T < ruinTime X x D ω then
      (dividendMeasure D ω) ({T} : Set ℝ) *
        ENNReal.ofReal (Real.exp (-(q * T))) else 0 ∂P) := by sorry
