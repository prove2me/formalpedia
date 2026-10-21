-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_rps_isRandAlloc
-- name    : ExAnteExPost.RPS.rps_isRandAlloc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:50.628571+00:00
-- url     : https://prove2.me/theorems/18d16e87-31c9-406b-969f-bcb0b725b6e5
-- title:
--   §3.1, p. 9 — Algorithm 1 returns an integral allocation in every execution: its output is a randomized allocation
-- statement:
--   Fix an instance with $n \ge 1$ agents, a favorite-good choice rule and an admissible decomposition rule. For every number of stages $T$ and every set of goods $M'$, the output of $T$ stages of Algorithm 1 started from $M'$ is a randomized allocation:
--
--   1. every probability lies in $[0,1]$ and the probabilities sum to $1$;
--   2. every allocation in the list is integral, with pairwise disjoint bundles;
--   3. every bundle is contained in $M'$.
--
--   In particular Algorithm 1 itself ($T = \lceil m/n \rceil$, $M' = M$) returns a randomized allocation, so the ex-ante statement of Theorem 2 is about a genuine lottery.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 9, §3.1

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- §3.1, p. 9: any number `T` of stages of Algorithm 1 on `M'` produce a randomized
allocation (probabilities in `[0,1]` summing to one, disjoint bundles) whose bundles lie in `M'`. -/
theorem rps_isRandAlloc [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D)
    (T : ℕ) (M' : Finset G) :
    IsRandAlloc (rps pick D T M') ∧ ∀ e ∈ rps pick D T M', ∀ i, e.2 i ⊆ M' := by sorry
end ExAnteExPost.RPS
