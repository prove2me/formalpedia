-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:25:40.531209+00:00
-- url     : https://prove2.me/theorems/724e387f-af08-4400-ac51-2b29d7314d93
-- title:
--   Finite expected original full Stieltjes cash makes unbounded finite random-clock signed real reward L1
-- statement:
--   For the exact original Lévy process, admissible dividend strategy D, original P and dividendMeasure, if the full outer expected ENNReal ruin-stopped Stieltjes payout at any measurable pathwise finite random clock τ is finite, then the genuine signed real discounted Stieltjes reward over the identical paymentTimes(ruinTime)∩Iic τ is P-integrable. This requires no deterministic bound on τ. It consumes the original cash-toReal L1 lemma and the already Proved pathwise equality of original real and ENNReal Stieltjes integrals, plus positivity of exp. Time-zero right-limit, all continuous mass and random clock endpoint atoms are retained.
-- source:
--   Original real horizon pathwise full Stieltjes equality and companion finite random-clock cash-toReal L1 theorem; Mathlib Integrable.congr, ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_toReal_cash_L1_of_full_ennreal_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
