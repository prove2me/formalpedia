-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_cash_mean_eq_signed_stieltjes_mean
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_toReal_cash_mean_eq_signed_stieltjes_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:31:41.096714+00:00
-- url     : https://prove2.me/theorems/e1f31472-bc20-49f4-9e26-472dd7cdaef6
-- title:
--   Original bounded random-clock expected ENNReal cash.toReal equals genuine signed Stieltjes mean
-- statement:
--   At the actual original admissible capped Levy dividend process and any bounded measurable nonnegative random clock, the P-expectation of the ENNReal stopped cash converted by toReal agrees exactly with the P-expectation of the real discounted Stieltjes integral over the same paymentTimes(ruinTime)∩Iic(τ ω) and original dividendMeasure. The proof is pathwise using the accepted exact real-horizon full Stieltjes bridge, real exponential positivity and ENNReal.toReal_ofReal, followed by integral_congr_ae. The accepted original random-clock L1 theorem ensures these are genuine finite real expectations under admissibility, without proxy model or dropped time-zero atom.
-- source:
--   Proved W7-03 exact real-horizon pathwise signed/ENNReal Stieltjes equality cabfeef5; original bounded clock cash L1 results; Mathlib ENNReal.toReal_ofReal.

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

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_toReal_cash_mean_eq_signed_stieltjes_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫ ω, (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
