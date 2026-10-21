-- Prove2me | Theorems.Thm_ConsHalving_Additive_theorem_2_2
-- name    : ConsHalving.Additive.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:51.559123+00:00
-- url     : https://prove2.me/theorems/215b1f69-b64b-4176-82fc-2ce8d3a15cb9
-- title:
--   Theorem 2.2, p. 4 — for additive utilities a consensus halving cutting at most min{n, m} items exists
-- statement:
--   Let $n$ agents have additive, nonnegative utilities $u_i(j)\ge 0$ over $m$ items. Then there is a consensus halving that cuts at most $\min\{n,m\}$ items: a vector $x\in[0,1]^m$ with
--   $$\sum_{j} x_j\,u_i(j)=\sum_{j}(1-x_j)\,u_i(j)\quad\text{for every agent } i,\qquad \#\{j:\ 0<x_j<1\}\le\min\{n,m\}.$$
--   Here one part holds the fraction $x_j$ of item $j$ and the other part the fraction $1-x_j$.
--
--   Splitting every item in half always gives a consensus halving, but with $m$ cuts; the theorem says that, however many items there are, at most as many items as there are agents need to be split.
--
--   **Formalization Note** The paper's Theorem 2.2 asserts that a polynomial-time algorithm *computes* such a consensus halving. The paper fixes no machine model (its complexity argument is "via Gaussian elimination"), so only the existence of the output is formalized; the algorithm's steps are the milestones of the mission. Agents and items are indexed by `Fin n`, `Fin m`, and $n,m\ge 1$ is not assumed (for $m=0$ or $n=0$ the statement remains true).
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 4, Theorem 2.2

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem theorem_2_2 {n m : ℕ} (u : Fin n → Fin m → ℝ) (hu : ∀ i j, 0 ≤ u i j) :
    ∃ x : Fin m → ℝ, IsConsensusHalving u x ∧ numCuts x ≤ min n m := by sorry

end ConsHalving.Additive
