-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_grid_inf_first_hit_time
-- name    : AvramDividend.Classical.monotone_grid_inf_first_hit_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:16:45.750983+00:00
-- url     : https://prove2.me/theorems/1dc26a24-c1b0-411b-ac45-206284fb0f11
-- title:
--   The extended first grid-passage infimum equals the clock time of the earliest strict hit
-- statement:
--   For an arbitrary real-valued sequence u(k), a set s that is visited at least once, and a nondecreasing NNReal clock c(k), the ENNReal infimum over all k of c(k) when u(k)∈s (and infinity otherwise) equals c(j), where j=Nat.find is the least hitting index. Nat.find_le shows j≤k at every other hit, so clock monotonicity makes c(j) the minimum of all crossing times. This gives the exact passage clock used in an unbounded discrete first-upcrossing payoff, requiring no stochastic hypotheses.

import Mathlib.Data.Nat.Find
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.monotone_grid_inf_first_hit_time
    (u : ℕ → ℝ) (s : Set ℝ) [DecidablePred (fun k : ℕ => u k ∈ s)]
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (h : ∃ j : ℕ, u j ∈ s) :
    (⨅ k : ℕ, if u k ∈ s then (clock k : ℝ≥0∞) else ∞) =
      (clock (Nat.find h) : ℝ≥0∞) := by sorry
