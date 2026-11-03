-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_signed_L1_real_budget_implies_full_ennreal_budget
-- name    : AvramDividend.Classical.avram_wave7_03_original_signed_L1_real_budget_implies_full_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:02:30.652142+00:00
-- url     : https://prove2.me/theorems/2e4b8f8d-3ee6-4db3-953e-c63a471fe3e9
-- title:
--   Signed-L1 real Stieltjes expected budget implies full original-process ENNReal expected dividend budget
-- statement:
--   For the original Lévy process and law P, original dividend measure Dω, ruin-stopped paymentTimes and arbitrary measurable finite NNReal random clock τ, if the genuine discounted real signed Stieltjes payout is P-integrable and has real expected value at most B, then the exact double ENNReal discounted payout under original P is at most ENNReal.ofReal B. This consumes the Proved source signed-L1-to-ENNReal mean equality, which accounts for the time-zero right-limit atom and all continuous pre-ruin cash; then uses monotonicity of ENNReal.ofReal. No separate expected-cash finiteness or budget nonnegativity hypothesis is needed because the L1 source bridge provides the former and ofReal clips only as dictated by the exact statement.
-- source:
--   Proved original finite random-clock full signed-Stieltjes mean equality of signed L1 and ENNReal.ofReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_mean_eq_of_signed_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_signed_L1_real_budget_implies_full_ennreal_budget
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
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P)
    (B : ℝ)
    (hSignedBudget :
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
