-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:04:34.585434+00:00
-- url     : https://prove2.me/theorems/c278d47c-3d5b-4cd1-8c45-2c8bd741d922
-- title:
--   Original finite random-clock expected ENNReal fibre toReal payout equals original signed Stieltjes expected payout
-- statement:
--   For the original spectrally negative Lévy process on Ω under P, canonical dividendMeasure D ω and the ruin-stopped paymentTimes interval up to a measurable finite NNReal sample-dependent clock τ, the outer P-integral of the exact ENNReal fibre payout converted toReal equals the outer P-integral of the genuine discounted signed real Stieltjes payout. Proved pathwise source real-horizon Stieltjes equality at T=τ ω and positivity of the real exponential imply pointwise equality including all time-zero right-limit and strictly pre-ruin continuous cash. Equality of the outer real integrals follows by integral_congr_ae. The theorem requires no global cash finiteness or L1 hypothesis, but makes no assertion that those outer real expectations are finite without an additional integrability theorem.
-- source:
--   Proved source real-horizon full signed/ENNReal pathwise equality and Mathlib integral_congr_ae, integral_nonneg, ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hDiv : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫ ω, (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
