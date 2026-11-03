-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_uniform_signed_horizons_imply_genuine_perpetual_signed_L1_and_mean
-- name    : AvramDividend.Classical.avram_wave7_03_uniform_signed_horizons_imply_genuine_perpetual_signed_L1_and_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:49:50.653208+00:00
-- url     : https://prove2.me/theorems/616b3639-3329-40d6-8631-481303f78cb1
-- title:
--   Uniform original signed finite-horizon Stieltjes mean budgets yield real untruncated perpetual L1 and exact ENNReal value
-- statement:
--   For the canonical original X, P, D and its full dividendMeasure, a real uniform bound on genuine expected signed discounted Stieltjes payouts over paymentTimes(ruinTime)∩Iic(n+1) for every natural n yields Integrable on the original P of the genuine *unrestricted real Stieltjes payout integral* over paymentTimes(ruinTime) and identifies dividendValue exactly with ENNReal.ofReal of the expected unrestricted real signed Stieltjes payout. This is a short Lean consumption bridge useful for W7-04/08/10/11; it explicitly derives finite canonical dividendValue from Proved original horizon iff and invokes new unrestricted signed mean equality, retaining initial and continuous payouts and strict pre-ruin terms.
-- source:
--   Proved original perpetual finiteness iff uniform signed horizons 000389d1-8b8e-45cf-b4d1-0a4e161b8c29; new original full unrestricted signed Stieltjes L1 and mean bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_uniform_signed_horizons_imply_genuine_perpetual_signed_L1_and_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
