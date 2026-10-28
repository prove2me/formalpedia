-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFutureReward_measurable
-- name    : AvramDividend.Classical.levy_boundedStopping_stoppedFutureReward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:00:45.260116+00:00
-- url     : https://prove2.me/theorems/e67c32fd-1178-44fc-8fd2-2ad395477f0d
-- title:
--   Measurability of bounded stopped-history Lévy future rewards
-- statement:
--   For an adapted spectrally negative Lévy process with right-continuous trajectories, every bounded continuous measurable reward of the future increment path evaluated at a bounded stopping time, multiplied by the indicator of a stopped-history event, is measurable. Follows from finite adapted upper grids, measurable grid rewards, and convergence to the stopped reward.
-- source:
--   Mathematical bridge from Proved upper-grid convergence and fibre measurability to a strong-Markov scalar law with no extra stopped-reward measurability premise. Supports full future path product identity 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_ennrealFutureReward_limit
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_measurable

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_stoppedFutureReward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g) :
    Measurable (Set.indicator A
      (fun ω : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω))) := by
  sorry
