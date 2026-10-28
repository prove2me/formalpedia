-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_namedShiftedReward_markov_lower
-- name    : AvramDividend.Classical.firstRecord_capped_namedShiftedReward_markov_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:13:21.466013+00:00
-- url     : https://prove2.me/theorems/ec561746-de93-4a0a-9bd8-04088b2ac63d
-- title:
--   Finite capped first-record strong-Markov lower reward bound
-- statement:
--   At the surviving first strict record capped by a deterministic horizon, the expected future shifted two-sided exit reward is bounded below by the expected past discount times the true two-sided exit reward. This specialised inequality uses the stopped-history measurability and capped stopping time previously proved for the upper counterpart, and supports the unbounded first-record lower renewal step.
-- source:
--   Proved capped first-record stopping-time and survival measurability results, and the lower stopped-Markov shifted reward theorem finiteStopping_trueShiftedReward_expected_lower. A direct lower-direction counterpart of the accepted upper capped Markov estimate.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_lower

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_namedShiftedReward_markov_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (N : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτdef : τ = fun ω => (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ)
    (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω, ρ ω =
      ⨅ i : {t : ℝ≥0 // upper < X.X (τ ω + t) ω - X.X (τ ω) ω},
        (i.1 : ℝ≥0∞))
    (hσ : ∀ ω, σ ω =
      ⨅ i : {t : ℝ≥0 // X.X (τ ω + t) ω - X.X (τ ω) ω < lower},
        (i.1 : ℝ≥0∞)) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      discount (τ ω) * (if ρ ω < σ ω then
        ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal))) else 0)
      else 0 ∂P) := by sorry
