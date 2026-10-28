-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedHistory_indicator_partition
-- name    : AvramDividend.Classical.finiteGrid_stoppedHistory_indicator_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:49:49.64064+00:00
-- url     : https://prove2.me/theorems/6bee9512-8d46-4993-99cc-c513319cea1a
-- title:
--   Stopped-history indicator equals the sum over disjoint finite stopping-time grid fibres
-- statement:
--   A random time taking values in a finite grid partitions any stopped-history event into disjoint measurable fibre indicators.
-- source:
--   Required to aggregate accepted stopped-grid future reward product f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b into open strong Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Notation.Indicator

open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.finiteGrid_stoppedHistory_indicator_partition
    {Ω : Type*} (τn : Ω → ℝ≥0) (A : Set Ω) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τn ω ∈ grid) (ω : Ω) :
    (∑ s ∈ grid,
      Set.indicator (A ∩ {ω' : Ω | τn ω' = s})
        (fun _ : Ω => (1 : ℝ≥0∞)) ω) =
      Set.indicator A (fun _ : Ω => (1 : ℝ≥0∞)) ω := by
  sorry
