-- Prove2me | Theorems.Thm_Balinski61_Whitney_disjoint_paths_of_integral_flow
-- name    : Balinski61.Whitney.disjoint_paths_of_integral_flow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:05:52.932056+00:00
-- url     : https://prove2.me/theorems/48477297-0e7f-42dd-8803-180e2136c884
-- title:
--   p. 434, proof of WHITNEY'S THEOREM — an integral flow of value at least n gives n disjoint paths
-- statement:
--   Let $G$ be a finite graph, $p_s \ne p_k$ two of its points and $n \ge 0$ an integer, and give $G$ the capacities of Whitney's proof: $1$ on every point except $p_s, p_k$ (which get $n+1$), $n+1$ on every line except the line $p_sp_k$ (if present), which gets $1$. If $f$ is a flow from $p_s$ to $p_k$ in this network whose path flows are all integers and whose value is at least $n$,
--   $$
--   f(C) \in \mathbb Z \ \text{ for all } C, \qquad \operatorname{val}(f) \ge n,
--   $$
--   then $G$ has $n$ disjoint paths from $p_s$ to $p_k$ (pairwise distinct simple paths sharing no point other than $p_s$ and $p_k$).
--
--   This is the step "no two unit path flows can go through one point, due to the capacity restrictions" of the paper.
--
--   **Formalization Note** The flow need not be maximum; only integrality and value $\ge n$ are used. The capacity $1$ on the line $p_sp_k$ is what prevents the single-line path from being counted more than once.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 434, proof of WHITNEY'S THEOREM

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph
import Definitions.Def_Balinski61_Whitney_Network
import Definitions.Def_Balinski61_Whitney_UnitNetwork

namespace Balinski61.Whitney

theorem disjoint_paths_of_integral_flow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (ps pk : V) (hst : ps ≠ pk)
    (f : G.Path ps pk → ℝ) (hf : IsFlow G (unitCapV ps pk n) (unitCapE ps pk n) ps pk f)
    (hint : ∀ C, ∃ z : ℤ, f C = z) (hval : (n : ℝ) ≤ flowValue G f) :
    HasNDisjointPaths G n ps pk := by sorry

end Balinski61.Whitney
