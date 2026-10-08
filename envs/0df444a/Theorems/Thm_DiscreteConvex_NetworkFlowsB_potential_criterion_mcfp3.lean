-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsB_potential_criterion_mcfp3
-- name    : DiscreteConvex.NetworkFlowsB.potential_criterion_mcfp3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:32:38.976575+00:00
-- url     : https://prove2.me/theorems/a5c2bd26-fde8-485f-b2d7-e8fc27747c75
-- title:
--   Theorem 9.4 -- potential_criterion_mcfp3
-- statement:
--   **Theorem 9.4** (Potential criterion; p.249-250). GOAL. In the minimum cost flow problem MCFP3 with polyhedral convex $f$ and $f_a$ ($a\in A$): (1) for a feasible flow $\xi$, $\xi$ is optimal iff there is a potential $p$ satisfying conditions (i)-(ii) of (POT); (2) any optimal potential for one optimal flow characterizes optimality of every feasible flow.
--
--   This is the theorem the rest of this mission's results build on: Theorem 9.14 is stated by the book as "immediate from Theorem 9.4", and Theorems 9.5, 9.6, 9.15, 9.16, 9.18, 9.20 all cite it or a direct corollary of it as their starting point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249-250, Theorem 9.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.249-250, Theorem 9.4

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.4 (Potential criterion; p.249-250). GOAL. In the minimum cost flow problem MCFP3
with polyhedral convex `f` and `fa` (`a ∈ A`): (1) for a feasible flow `ξ`, `ξ` is optimal iff
there is a potential `p` satisfying (i)-(ii) of (POT); (2) any optimal potential for one optimal
flow characterizes optimality of every feasible flow. -/
theorem potential_criterion_mcfp3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hfa : ∀ a, IsPolyhedralConvexArc (fa a)) :
    (∀ xi, FeasibleFlowMCFP3 tail head fa f xi →
      (OptimalFlowMCFP3 tail head fa f xi ↔ ∃ p : V → ℝ, IsOptimalPotential tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMCFP3 tail head fa f xi → IsOptimalPotential tail head fa f xi p →
      ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' →
        (OptimalFlowMCFP3 tail head fa f xi' ↔ IsOptimalPotential tail head fa f xi' p)) := by sorry

end DiscreteConvex.NetworkFlowsB
