-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_lintegral_decomposition
-- name    : AvramDividend.Classical.finiteGrid_stoppedReward_lintegral_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:58:31.777704+00:00
-- url     : https://prove2.me/theorems/d7b9d4a5-11f7-49f0-8415-4da63551b075
-- title:
--   Lévy stopped dividend reward integrates as the sum over finite adapted stopping-time fibres
-- statement:
--   For an arbitrary nonnegative future-dependent reward evaluated at a stopping time taking values in a finite grid, the expected reward restricted to event A equals the sum of expected rewards on each disjoint stopping-time fibre, provided those fibre rewards are measurable. This is the integral-level aggregation step for the established finite-grid strong-Markov factorisation.
-- source:
--   Root-connected mathematical intermediate for AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent (61930a38-11f1-449e-bbb6-67d59c6d5ca8), which in turn is needed for W-free barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380. Composes proved fibre-decomposition 7f2c3e14-bf0e-4449-8451-201d3ef241e9 with the nonnegative integral's finite-sum property.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_fibre_decomposition

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.finiteGrid_stoppedReward_lintegral_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τn : Ω → ℝ≥0) (A : Set Ω)
    (grid : Finset ℝ≥0) (hgrid : ∀ ω, τn ω ∈ grid)
    (f : ℝ≥0 → Ω → ℝ≥0∞)
    (hMeas : ∀ s ∈ grid,
      Measurable (Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s))) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => f (τn ω') ω') ω ∂P) =
      ∑ s ∈ grid, ∫⁻ ω,
        Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s) ω ∂P := by
  sorry
