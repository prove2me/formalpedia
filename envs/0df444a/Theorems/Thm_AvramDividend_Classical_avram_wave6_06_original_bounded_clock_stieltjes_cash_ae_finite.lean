-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
-- name    : AvramDividend.Classical.avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:05:36.163207+00:00
-- url     : https://prove2.me/theorems/e1455beb-b5b2-4e36-afc2-d20336b64128
-- title:
--   Original ruin-stopped dividend reward is almost surely finite at every bounded random clock
-- statement:
--   For the actual source spectrally negative Lévy process and original admissible dividend D, the full paymentTimes(ruinTime) discounted Stieltjes cash restricted to the closed random clock interval (-∞,τ(ω)] is finite P-almost surely whenever the random clock has deterministic finite upper bound T. This retains all right-dividend atoms including the terminal one, singular-continuous payouts, time-zero payments, and original ruin restriction. No stochastic calculus assumption or independence beyond the given source is needed: compare pathwise with the already Proved full deterministic-horizon source cash result f0d4c94c via lintegral_mono_set.
-- source:
--   Original bounded random stop source-cash finiteness bridge for Chat 06 b02af371 hCashFinite. Provider f0d4c94c is Proved; the horizon restriction is exact with Iic τ. No use of the missing Ito-Meyer chain identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
