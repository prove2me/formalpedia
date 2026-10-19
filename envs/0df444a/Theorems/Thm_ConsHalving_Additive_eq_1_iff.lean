-- Prove2me | Theorems.Thm_ConsHalving_Additive_eq_1_iff
-- name    : ConsHalving.Additive.eq_1_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:46.380608+00:00
-- url     : https://prove2.me/theorems/2087dbd3-d88e-4c8b-b8c3-56953a71a8ab
-- title:
--   (1), p. 4 — under additivity, x is one part of a consensus halving iff Σ_j x_j u_i(j) = ½ Σ_j u_i(j) for all i
-- statement:
--   Let $n$ agents have additive utilities $u_i(j)$ over $m$ items, and let $x\in\mathbb R^m$ give the fraction $x_j$ of item $j$ in one part $M'$, the other part holding $1-x_j$. Then the two parts have equal value for every agent if and only if $x$ satisfies the system (1):
--   $$\Big(\forall i:\ \sum_{j} x_j\,u_i(j)=\sum_j (1-x_j)\,u_i(j)\Big)\iff\Big(\forall i:\ \sum_{j} x_j\,u_i(j)=\frac12\sum_{j}u_i(j)\Big).$$
--
--   This turns the equal-value condition of Definition 2.1 into $n$ linear equations in $x$, which is the linear system the algorithm of Theorem 2.2 works with.
--
--   **Formalization Note** No bound $x_j\in[0,1]$ and no sign condition on the utilities is assumed; the equivalence is pure linear algebra and holds without them.
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 4, (1)

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem eq_1_iff {n m : ℕ} (u : Fin n → Fin m → ℝ) (x : Fin m → ℝ) :
    (∀ i, util u i x = util u i (fun j => 1 - x j)) ↔
      ∀ i, ∑ j, x j * u i j = (1 / 2) * ∑ j, u i j := by sorry

end ConsHalving.Additive
