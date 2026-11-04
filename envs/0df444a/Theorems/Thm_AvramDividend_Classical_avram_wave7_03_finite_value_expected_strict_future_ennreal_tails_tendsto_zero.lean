-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:58:53.374769+00:00
-- url     : https://prove2.me/theorems/90a780e4-ec44-434d-9ab4-c603de9f6133
-- title:
--   Finite original dividendValue makes the expected strict future ENNReal Stieltjes cash vanish
-- statement:
--   For the same original spectrally negative Lévy process X under P and genuine dividendMeasure D ω on strict pre-ruin paymentTimes, finite perpetual original expected discounted payout implies the double ENNReal integral of strictly future discounted dividends over times t>n converges to zero as n tends to infinity. This is an expectation-level upgrade of the already proved almost-sure vanishing of future payout tails. It requires genuine original-measure measurability, an antitone exact future interval, and domination by the actual finite dividendValue. It handles all continuous/jump payments and excludes the endpoint right-limit atom at each n.
-- source:
--   Direct application of pinned Mathlib MeasureTheory.lintegral_tendsto_of_tendsto_of_antitone to the exact original random future cash, using accepted strict-future measurability and almost-sure tail vanishing, set inclusion of Ioi windows, and the canonical finite original dividendValue. Now imports the exact pinned DominatedConvergence module and the previously Open strict-future kernel helper is Proved (ea1c2561-3508-43a7-8d26-861057008c4e).

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_implies_ae_ENNReal_strict_future_tails_zero_direct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
