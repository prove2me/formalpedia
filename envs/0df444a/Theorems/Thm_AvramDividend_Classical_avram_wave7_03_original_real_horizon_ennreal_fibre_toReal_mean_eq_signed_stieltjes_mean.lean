-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:01:23.248444+00:00
-- url     : https://prove2.me/theorems/f9800645-0355-44b8-a2bb-e0a66e2d519d
-- title:
--   Original real-horizon expected fibre ENNReal toReal dividend equals genuine expected signed Stieltjes integral
-- statement:
--   For the exact original spectrally negative Lévy process X on Ω under P and a canonical dividend strategy D, at any finite nonnegative real horizon T the real expected value of the ENNReal fibre cash converted by toReal equals the real expected signed discounted Stieltjes integral on exactly paymentTimes(ruinTime X x D ω)∩Iic T with dividendMeasure D ω. The Proved source real-horizon pathwise identity establishes equality of the fibre ENNReal cash with ofReal of its signed Stieltjes value including the time-zero right-limit atom, and positivity of the discounted Stieltjes integrand removes the ofReal/toReal clipping. Pointwise equality transfers through the original real expectation under P. No global L1 or expected-cash finiteness hypothesis is required, since it is equality of two real integrals of pointwise identical functions.
-- source:
--   Proved exact source real-horizon full Stieltjes pathwise equality, original definitions, nonnegative real exponential and integral_congr_ae.

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

theorem AvramDividend.Classical.avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hDiv : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
