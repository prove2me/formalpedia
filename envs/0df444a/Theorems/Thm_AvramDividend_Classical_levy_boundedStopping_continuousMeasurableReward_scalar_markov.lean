-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_continuousMeasurableReward_scalar_markov
-- name    : AvramDividend.Classical.levy_boundedStopping_continuousMeasurableReward_scalar_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:09:27.337986+00:00
-- url     : https://prove2.me/theorems/8d0c23a1-5f8d-4adc-b41f-f7b572a6d3b1
-- title:
--   Strong-Markov expectation at bounded stopping times for continuous measurable path rewards
-- statement:
--   For bounded stopping times and stopped-history events, any bounded future-path reward that is both continuous in the product topology and measurable in the coordinate sigma-algebra has a factored strong-Markov expectation. The explicit measurability hypothesis is necessary for the uncountably-indexed product measurable space: continuity alone does not provide Lean's OpensMeasurableSpace instance.
-- source:
--   Direct continuous-time strong-Markov bridge from finite-grid factorisation and pathwise convergence for Open Lévy shifted-path law 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and dividend barrier split 79978d61-9d1f-4b20-b8a5-114797a8e380. Correction of missing OpensMeasurableSpace (NNReal → Real) in direct candidate 15074 by requiring the mathematically relevant measurable reward separately.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_ennrealFutureReward_limit
import Theorems.Thm_AvramDividend_Classical_levy_upperGrid_stoppedHistory_scalar_markov
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_measurable
import Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_reward_tendsto_of_bounded
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_continuousMeasurableReward_scalar_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
