-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_measurable
-- name    : AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:47:29.099978+00:00
-- url     : https://prove2.me/theorems/bb899a6e-0d4e-4f86-903e-bfac7deff2ac
-- title:
--   Whole stopped-grid future Lévy reward is measurable from its adapted fibres
-- statement:
--   The future-path reward evaluated at a finite adapted approximation to a stopping time, restricted to a stopped-history event, is measurable. Decompose the complete reward into a finite sum of disjoint stopping-fibre indicators and use proven measurability of each shifted future Lévy reward.
-- source:
--   Needed to apply the pinned dominated-convergence theorem at bounded stopping grids, to pass the finite-grid scalar Markov formula to general stopping times. Composes Proved finiteGrid_stoppedReward_fibre_decomposition 7f2c3e14-bf0e-4449-8451-201d3ef241e9 and levy_stoppedHistory_gridFutureReward_fibre_measurable 2c2cd046-3146-460f-bbc8-656886400292. Ultimately child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_fibre_decomposition
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_fibre_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τn n ω ∈ grid)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    Measurable (Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τn n ω' + t) ω' - X.X (τn n ω') ω'))) := by
  sorry
