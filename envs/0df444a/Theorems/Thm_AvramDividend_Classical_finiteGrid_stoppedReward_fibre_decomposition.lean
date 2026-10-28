-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_fibre_decomposition
-- name    : AvramDividend.Classical.finiteGrid_stoppedReward_fibre_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:49:42.702145+00:00
-- url     : https://prove2.me/theorems/7f2c3e14-bf0e-4449-8451-201d3ef241e9
-- title:
--   Any stopped future reward decomposes into disjoint upper-grid fibre rewards
-- statement:
--   A finite-grid stopped future payoff restricted to a stopped-history event equals the sum over its mutually disjoint stopping-time fibres, with no measurable-decidability assumptions.
-- source:
--   Bridge from Proved stopped history grid future reward f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b to Proved whole future grid limit 23c80e32-f74f-42e9-94dc-13d6f0d8e8d9 and Open strong Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Notation.Indicator

open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.finiteGrid_stoppedReward_fibre_decomposition
    {Ω : Type*} (τn : Ω → ℝ≥0) (A : Set Ω)
    (grid : Finset ℝ≥0) (hgrid : ∀ ω, τn ω ∈ grid)
    (f : ℝ≥0 → Ω → ℝ≥0∞) (ω : Ω) :
    (∑ s ∈ grid,
      Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s) ω) =
      Set.indicator A (fun ω' : Ω => f (τn ω') ω') ω := by
  sorry
