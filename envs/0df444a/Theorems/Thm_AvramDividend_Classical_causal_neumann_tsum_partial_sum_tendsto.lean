-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_tsum_partial_sum_tendsto
-- name    : AvramDividend.Classical.causal_neumann_tsum_partial_sum_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:57:41.980515+00:00
-- url     : https://prove2.me/theorems/5128dbe1-4ed4-430e-8bb1-bebdd23e1c52
-- title:
--   Summable Gaussian Neumann corrections converge through every finite prefix
-- statement:
--   For a pointwise summable family of Gaussian Neumann corrections Q, the finite sums through index n converge to the function defined by their infinite sum. This closes the hS convergence hypothesis in the causal derivative-resolvent limit theorem.
-- source:
--   Apply Mathlib Summable.tendsto_sum_tsum_nat and compose with the natural-number shift n↦n+1. This provides the exact hS limit premise required by causal_neumann_resolvent_dominated_convergence, using the summability proved by causal_geometric_neumann_summable.

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Pi
open Filter

theorem AvramDividend.Classical.causal_neumann_tsum_partial_sum_tendsto
    (Q : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hQ : ∀ x : ℝ, Summable (fun n : ℕ => Q n x))
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x) :
    ∀ x : ℝ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) x)
      atTop (nhds (g x)) := by sorry
