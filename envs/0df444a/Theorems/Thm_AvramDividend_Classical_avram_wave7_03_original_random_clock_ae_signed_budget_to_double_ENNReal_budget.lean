-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_clock_ae_signed_budget_to_double_ENNReal_budget
-- name    : AvramDividend.Classical.avram_wave7_03_original_random_clock_ae_signed_budget_to_double_ENNReal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:08:20.515912+00:00
-- url     : https://prove2.me/theorems/b029d3a3-e206-449e-bed3-e78284821cad
-- title:
--   Exact original-process random-clock a.e signed Stieltjes pathwise bound yields the outer double ENNReal cash bound
-- statement:
--   For the actual original spectrally negative Lévy process X with original P, ruinTime, paymentTimes and dividendMeasure, fix any real-valued random clock τ and random real bound B. If the genuine signed discounted Stieltjes integral is IntegrableOn the precisely same pre-ruin ∩ Iic(τ ω) subwindow P-almost surely and is almost surely ≤B ω, then the outer P ENNReal expectation of the true inner discounted Stieltjes cash is ≤ the outer expectation of ENNReal.ofReal(B ω). Includes time-zero right-limit and random-horizon rightpayment atoms, all continuous and jump payouts. Explicit a.e integrability is necessary for the signed bridge; the proof does not assert a stochastic HJB budget.
-- source:
--   Pinned exact Mathlib ofReal_integral_eq_lintegral_ofReal, ENNReal.ofReal_le_ofReal and lintegral_mono_ae; original Definitions and process.

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

theorem AvramDividend.Classical.avram_wave7_03_original_random_clock_ae_signed_budget_to_double_ENNReal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ B : Ω → ℝ)
    (hInt : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω))
        (dividendMeasure D ω))
    (hSigned : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (B ω) ∂P) := by sorry
