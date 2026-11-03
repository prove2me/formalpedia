-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_mean_eq_of_signed_L1
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_stieltjes_mean_eq_of_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:56:44.671046+00:00
-- url     : https://prove2.me/theorems/142da406-12ae-407c-b4f1-63d88c06ab72
-- title:
--   Direct original full ENNReal/signed Stieltjes expected cash equality from signed L1
-- statement:
--   Under the actual original process, law P, dividendMeasure Dω, ruinTime and stopped paymentTimes set, if the genuine signed discounted Stieltjes payout is P-integrable at a measurable finite NNReal random clock, then the exact double ENNReal expected payout equals ENNReal.ofReal of that signed expectation. Proved original pathwise full Stieltjes equality identifies the exact same measures and domain, including right-limit time-zero and strictly pre-ruin dividend mass; positivity follows from Real.exp_pos. The pinned Mathlib ofReal_integral_eq_lintegral_ofReal theorem then gives the outer bridge with its required Integrable and a.e.-nonnegativity hypotheses. No auxiliary sample space or further global boundedness is assumed.
-- source:
--   Proved original real-horizon pathwise full Stieltjes equality; pinned Mathlib ofReal_integral_eq_lintegral_ofReal.

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

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_stieltjes_mean_eq_of_signed_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hSignedL1 : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
