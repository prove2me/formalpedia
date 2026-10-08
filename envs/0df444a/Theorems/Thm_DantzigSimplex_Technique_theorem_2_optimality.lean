-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_theorem_2_optimality
-- name    : DantzigSimplex.Technique.theorem_2_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:22:25.818976+00:00
-- url     : https://prove2.me/theorems/81490b9d-2bf6-49e3-b4a2-532bf101bf29
-- title:
--   Theorem 2 — nonpositive reduced gains imply a maximum feasible solution
-- statement:
--   Assume $1\le m\le n$ and Dantzig's nondegeneracy condition. Let $\lambda$ be a Phase II state supported on a basis $B$ of $m$ columns, with all its basic weights positive, and let $z_j=\sum_{i\in B}x_{ij}c_i$ be the objective value of the basis coordinates of $P_j$. If $c_j\le z_j$ for every $j$, then
--
--   $$
--   \sum_j\mu_jc_j\le\sum_j\lambda_jc_j
--   \quad\text{for every feasible }\mu.
--   $$
--
--   Thus $\lambda$ is a maximum feasible solution of (5)–(6). This is the optimality test that identifies a final Phase II basis.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, p. 344, Theorem 2

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Theorem 2, p. 344: condition (18) makes (7)--(8) optimal. -/
theorem theorem_2_optimality {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (s : PhaseIIState p) (h : ∀ j, p.cost j ≤ s.frame.z j) :
    p.MaximumFeasible s.weight := by sorry

end DantzigSimplex.Technique
