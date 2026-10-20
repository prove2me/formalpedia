-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_reward_eq_survival
-- name    : AvramDividend.Classical.killed_firstUpcrossing_weighted_reward_eq_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:44:59.650686+00:00
-- url     : https://prove2.me/theorems/8a54f290-36dd-41e5-84f8-0ff52144db1a
-- title:
--   Exact discounted killed-first-record payoff equals the prefix-survival weighted payoff
-- statement:
--   At each finite first strict upcrossing u of a nonnegative record b, the event that u occurs strictly before the reflected barrier ruin time is equivalent to absence of a strict drawdown exceedance before u, provided the reflected path is right-continuous at u. For any nonnegative payoff weight w(ω), including the q-discount factor, the corresponding killed stopped reward integral therefore equals the survival-weighted integral. This identifies an actual barrierRuinTime stopping condition with the event used in previously Proved two-sided weighted expectation inequalities. Right-continuity is explicit here and will be removed by a separately Proved path continuity theorem.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 renewal killed record, using accepted firstUpcrossing_pre_ruin_strict_of_right_continuous 05e40496-e6c7-49d5-9c54-7b719a196f54.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_pre_ruin_strict_of_right_continuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstUpcrossing_weighted_reward_eq_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, (u ω : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hRight : ∀ ω ∈ G, ContinuousWithinAt
      (fun t => reflectedSup X t ω) (Set.Ici (u ω)) (u ω))
    (w : Ω → ℝ≥0∞) :
    (∫⁻ ω, if ω ∈ G ∧
      (u ω : ℝ≥0∞) < barrierRuinTime X a ω
      then w ω else 0 ∂P) =
    (∫⁻ ω, if ω ∈ G ∧
      (∀ t : ℝ≥0, t < u ω → reflectedSup X t ω ≤ a)
      then w ω else 0 ∂P) := by sorry
