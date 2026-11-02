-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope
-- name    : AvramDividend.Classical.avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:37:59.135192+00:00
-- url     : https://prove2.me/theorems/5b72d578-8fbe-415a-b8ba-f60d73ed7257
-- title:
--   Original full Stieltjes expected payoff envelope at arbitrary bounded random clock
-- statement:
--   For the actual original source spectrally negative Levy X and admissible full Stieltjes dividend strategy D, the expected full discounted dividendMeasure D reward on paymentTimes(ruinTime) intersect the closed random endpoint Iic τ is bounded by the explicit finite deterministic-horizon exponential envelope whenever τ≤T pathwise. No stopping-time assumption is needed for this measure domination. Reuses the Proved original deterministic real-horizon expected Stieltjes envelope f97e.../ba6b... and derives only the nested integrand domain inclusion. Includes zero time, creeping, singular continuous dividends and arbitrary real q; no Ito-Meyer or Stieltjes calculation repeated. This is a finite integrability envelope, not the desired w(x) verification budget.
-- source:
--   Proved Chat03 original expected full Stieltjes envelope ba6baffc-07f7-41f6-b84e-ffb6c1089a5c; original payment domain monotonicity in the random horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp
      (|X.ψ 1 - q| * (((((T : ℝ).toNNReal + 1 : ℝ≥0) : ℝ))))) *
    ENNReal.ofReal (Real.exp x) := by sorry
