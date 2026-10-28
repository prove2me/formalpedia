-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_reward_tendsto_of_bounded
-- name    : AvramDividend.Classical.lintegral_stoppedEvent_reward_tendsto_of_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:55:58.505925+00:00
-- url     : https://prove2.me/theorems/c18a8b5d-e322-4297-bae5-c2eab75ea472
-- title:
--   Dominated convergence of stopped-history expected nonnegative future rewards
-- statement:
--   For a measurable sequence of nonnegative rewards restricted to a stopped-history event A, pointwise convergence of rewards and a uniformly bounded integrable envelope imply convergence of the expected event-restricted rewards. This supplies the limiting step from finite upper stopping grids to continuous stopping times in the strong-Markov dividend valuation.
-- source:
--   Root-connected analytic limit helper for the full finite-grid strong-Markov scalar formula levy_upperGrid_stoppedHistory_scalar_markov and target levy_strongMarkov_shiftedPath_indep_stoppedEvent 61930a38-11f1-449e-bbb6-67d59c6d5ca8; later W-free dividendValue_barrierStrategy_upExit_split_of_standing 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses pinned Mathlib tendsto_lintegral_of_dominated_convergence.

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.lintegral_stoppedEvent_reward_tendsto_of_bounded
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (f : ℕ → Ω → ℝ≥0∞) (fLim : Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (Set.indicator A (f n)))
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (nhds (fLim ω)))
    (C : ℝ≥0∞) (hbound : ∀ n ω, f n ω ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    Tendsto
      (fun n => ∫⁻ ω, Set.indicator A (f n) ω ∂P)
      atTop
      (nhds (∫⁻ ω, Set.indicator A fLim ω ∂P)) := by
  sorry
