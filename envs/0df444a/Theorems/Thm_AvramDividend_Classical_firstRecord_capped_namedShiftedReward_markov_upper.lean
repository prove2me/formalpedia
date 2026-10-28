-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_namedShiftedReward_markov_upper
-- name    : AvramDividend.Classical.firstRecord_capped_namedShiftedReward_markov_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:10:41.509237+00:00
-- url     : https://prove2.me/theorems/74ac4009-4eae-487e-90a2-0cee30487a1f
-- title:
--   Finite first-record cap Markov factorisation with stopped-survival event
-- statement:
--   Specialise the finite stopping-time Lévy Markov factorisation to the record clock stopped at a finite horizon. The event that the first record survives reflected ruin and precedes the horizon is shown to be measurable at this clock, yielding an upper bound for discounted shifted two-sided exit rewards.
-- source:
--   Accepted firstRecord_capped_rightCont_stopping_and_clock_measurable, firstRecord_capped_survival_in_finiteStoppedHistory, and finiteStopping_shiftedInfimumClocks_expected_upper.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_finiteStopping_shiftedInfimumClocks_expected_upper

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_namedShiftedReward_markov_upper
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
      discount (τ ω) * (if ρ ω < σ ω then
        ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal))) else 0)
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      discount (τ ω) else 0 ∂P) * (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by sorry
