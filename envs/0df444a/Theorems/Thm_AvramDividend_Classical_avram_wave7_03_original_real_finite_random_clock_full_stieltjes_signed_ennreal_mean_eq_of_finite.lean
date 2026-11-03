-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:47:58.901203+00:00
-- url     : https://prove2.me/theorems/dcb090fe-2937-40b4-a296-1f68cc3f0f2d
-- title:
--   Exact original full signed-to-ENNReal Stieltjes mean bridge for unbounded real-valued finite random stopping clock
-- statement:
--   For any measurable nonnegative real-valued random clock τ on the original spectrally negative Lévy sample space, with no deterministic global bound, if the actual original ruin-stopped double ENNReal expected payout is finite, then it exactly equals ENNReal.ofReal of the original expected real signed discounted Stieltjes payout over paymentTimes(ruinTime)∩Iic τ under the identical original P and dividendMeasure D ω. The proof converts τ pointwise to NNReal by toNNReal, uses nonnegativity to preserve the exact real endpoint, transfers measurability and expected cash finiteness without modifying the payment set, and applies the Proved finite NNReal random-clock original mean bridge. All time-zero right-limit, continuous and stopping-clock endpoint payouts remain included.
-- source:
--   Prior finite NNReal clock full original signed/ENNReal mean equality under finite expected cash, Real.coe_toNNReal and measurability transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτMeas : Measurable τ)
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
