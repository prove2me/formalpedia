-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb54_original_true_horizon_reward_expected_from_asymptotic_same_clock
-- name    : AvramDividend.Classical.avram_bvb54_original_true_horizon_reward_expected_from_asymptotic_same_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:06:53.397194+00:00
-- url     : https://prove2.me/theorems/a607ba38-d0af-41c3-a648-07f871b9cfbe
-- title:
--   Original true-horizon Lévy strictly truncated cash expected bound from eventual same-clock epsilon source budgets
-- statement:
--   Use actual original BV finite-activity top-cap cash F(n): original discounted rightLimit dividend payments strictly before T-T/(n+2) plus the genuine surviving postpayment reward at the FULL horizon T. Assuming these original cash variables are integrable and their expectations eventually lie below w(x)+epsilon for every positive epsilon, the independently Proved original cash monotonicity theorem and elementary integral bridge imply the expected cash at every fixed n is at most w(x). This corrects the stopped-clock mismatch of the analytically suspect 28336ae5 pathwise lemma; its remaining stochastic burden is the genuine original asymptotic compensated Stieltjes source with terminal strip correction.
-- source:
--   Proved original source cash+full terminal monotonicity c5eeb765 and generic expectation epsilon bridge BVB53 1d961b00. Original Avram et al. 2007 Prop 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Corrected top-cap expected-value route with the original true-horizon
terminal payoff and strictly truncated source cash, using eventual epsilon
budgets instead of the invalid pathwise same-row premature compensated bound. -/

theorem AvramDividend.Classical.avram_bvb54_original_true_horizon_reward_expected_from_asymptotic_same_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    (∀ n, Integrable (F n) P) →
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in (atTop : Filter ℕ), (∫ ω, F m ω ∂P) ≤ w x + ε) →
    ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by sorry
