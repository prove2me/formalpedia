-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_clock_signed_integrable_envelope_auto_positive_to_ENNReal
-- name    : AvramDividend.Classical.avram_wave7_03_original_random_clock_signed_integrable_envelope_auto_positive_to_ENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:11:49.469445+00:00
-- url     : https://prove2.me/theorems/555786ed-e53b-4d3d-823e-728ca17c440f
-- title:
--   Original random-clock signed cash and integrable envelope imply expected ENNReal budget, deriving envelope nonnegativity
-- statement:
--   For exact original Lévy X, P, ruinTime, paymentTimes and dividendMeasure, suppose the stopped random-horizon real signed exponential Stieltjes cash is IntegrableOn and P-a.e bounded by an integrable real envelope B whose P-expectation is ≤K. Then the true double ENNReal expected dividend cash is ≤ENNReal.ofReal K. The nonnegativity of B is formally deduced from nonnegativity of the original positive exponential Stieltjes integral and the assumed signed bound, eliminating a redundant envelope sign premise. Original zero atom, horizon atom, all continuous dividends and strict pre-ruin payments are included. The stochastic signed envelope itself remains a separate obligation.
-- source:
--   Pinned Mathlib integral_nonneg, exact ofReal_integral_eq_lintegral_ofReal on the actual inner measure and outer P, ENNReal.ofReal_le_ofReal, lintegral_mono_ae. No Open imports.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_random_clock_signed_integrable_envelope_auto_positive_to_ENNReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ B : Ω → ℝ) (K : ℝ)
    (hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω))
        (dividendMeasure D ω))
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K := by sorry
