-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_coord_diff_le
-- name    : AssignmentGame.CoreCorners.core_coord_diff_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:24:45.612774+00:00
-- url     : https://prove2.me/theorems/6d6a0029-8254-4ab7-b39f-c62c92deba2f
-- title:
--   Sec. 3.3, p. 122 — coordinate differences of core vectors are bounded by $u^*_i - u_{*i}$ and $v^*_j - v_{*j}$
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and $a_{ij} \ge 0$. For a seller $i$ let $u^*_i$ and $u_{*i}$ be the highest and lowest payoff to $i$ over the core, and for a buyer $j$ let $v^*_j$ and $v_{*j}$ be defined likewise. Then any two core vectors $(u', v')$ and $(u'', v'')$ satisfy
--   $$|u'_i - u''_i| \le u^*_i - u_{*i} \quad \text{for all } i \in M, \qquad |v'_j - v''_j| \le v^*_j - v_{*j} \quad \text{for all } j \in N.$$
--
--   Combined with Theorem 3, these inequalities show that the two corners are the farthest-apart pair of core points for every distance that depends only on the absolute values of the coordinate differences , not only for Euclidean distance.
--
--   **Formalization Note** $u^*_i, u_{*i}, v^*_j, v_{*j}$ are the real supremum and infimum over the core (`uHi`, `uLo`, `vHi`, `vLo`); they are the true extrema because the core is nonempty and bounded (the other milestones).
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 122, Sec. 3.3 (displayed inequalities after the proof of Theorem 3)

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open Finset

namespace AssignmentGame.CoreCorners

/-- Sec. 3.3, p. 122: any two core vectors differ, in each coordinate, by at most the spread
between the highest and the lowest core payoff of that player. -/
theorem core_coord_diff_le {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (u' u'' : M → ℝ) (v' v'' : N → ℝ)
    (h' : (u', v') ∈ core a) (h'' : (u'', v'') ∈ core a) :
    (∀ i : M, |u' i - u'' i| ≤ uHi a i - uLo a i) ∧
    (∀ j : N, |v' j - v'' j| ≤ vHi a j - vLo a j) := by sorry

end AssignmentGame.CoreCorners
