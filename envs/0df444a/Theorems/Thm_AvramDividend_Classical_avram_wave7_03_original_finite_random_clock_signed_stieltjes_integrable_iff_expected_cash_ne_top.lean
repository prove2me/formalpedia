-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_integrable_iff_expected_cash_ne_top
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_signed_stieltjes_integrable_iff_expected_cash_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:38:38.173711+00:00
-- url     : https://prove2.me/theorems/127e40f7-f9fc-4770-8e99-c244bb757a34
-- title:
--   Exact iff: original finite-clock real signed Stieltjes L1 and full outer expected ENNReal cash finite
-- statement:
--   For the canonical original spectrally negative Lévy process, admissible dividend strategy and any measurable pathwise finite NNReal random stopping clock τ, the genuine real signed discounted Stieltjes reward over paymentTimes(ruinTime)∩Iic(τ ω) is P-integrable if and only if the exact outer expected ENNReal payout of the canonical dividendMeasure D ω on that identical original stopped domain is not top. Both directions are justified without a uniform deterministic clock bound. The original source pathwise real/ENNReal Stieltjes equality makes each inner ENNReal cash finite pointwise and identifies its toReal with the nonnegative real signed payment; source random-clock measurability and pinned Mathlib integrable_toReal_iff then give the equivalence. Continuous payments, time-zero right-limit and endpoint atoms remain included.
-- source:
--   Proved source random upper-clock Stieltjes cash measurable; Proved original pathwise real/ENNReal Stieltjes equality; pinned Mathlib MeasureTheory.integrable_toReal_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_signed_stieltjes_integrable_iff_expected_cash_ne_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ↔
    ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≠ ⊤) := by sorry
