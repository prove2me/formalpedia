-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_corners
-- name    : AssignmentGame.CoreCorners.core_corners
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:25:21.615982+00:00
-- url     : https://prove2.me/theorems/1171d57a-e203-4556-a1aa-7b4682d6d398
-- title:
--   Theorem 3 — the low-price corner $(u_*, v^*)$ and the high-price corner $(u^*, v_*)$ lie in the core and are farthest apart
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and let $a_{ij} \ge 0$ for $i \in M$, $j \in N$. Over all imputations $(u, v)$ in the core of the assignment game, let $u^*_i$ and $u_{*i}$ denote the highest and lowest payoffs to seller $i$, and let $v^*_j$ and $v_{*j}$ denote the highest and lowest payoffs to buyer $j$. Then:
--
--   1. the **low-price corner** $(u_*, v^*)$ is in the core;
--   2. the **high-price corner** $(u^*, v_*)$ is in the core;
--   3. no two imputations in the core are further apart than these two: for all $(u', v')$, $(u'', v'')$ in the core,
--   $$\sum_{i \in M} (u'_i - u''_i)^2 + \sum_{j \in N} (v'_j - v''_j)^2 \le \sum_{i \in M} (u_{*i} - u^*_i)^2 + \sum_{j \in N} (v^*_j - v_{*j})^2.$$
--
--   The theorem says that the core is elongated along the direction of market-wide price movements: at one end every seller receives the top core payoff and every buyer the bottom one, at the other the reverse, and these two points are poles of a diameter of the core.
--
--   **Formalization Note** Distance is the Euclidean distance on $\mathbb{R}^M \times \mathbb{R}^N$, stated through squared distances. The extremal payoffs are the real `sSup`/`sInf` over the core (`uHi`, `uLo`, `vHi`, `vLo`); the goal does not assume the core nonempty or bounded (those are milestones), and membership of the corners in the core shows that each extremum is attained.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 121, Theorem 3

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open Finset

namespace AssignmentGame.CoreCorners

/-- Theorem 3, p. 121: the low-price corner `(u_*, v^*)` and the high-price corner
`(u^*, v_*)` are in the core, and no two core vectors are further apart (in Euclidean
distance on `ℝ^M × ℝ^N`) than these two. -/
theorem core_corners {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (uLo a, vHi a) ∈ core a ∧ (uHi a, vLo a) ∈ core a ∧
    ∀ (u' u'' : M → ℝ) (v' v'' : N → ℝ), (u', v') ∈ core a → (u'', v'') ∈ core a →
      ∑ i, (u' i - u'' i) ^ 2 + ∑ j, (v' j - v'' j) ^ 2 ≤
        ∑ i, (uLo a i - uHi a i) ^ 2 + ∑ j, (vHi a j - vLo a j) ^ 2 := by sorry

end AssignmentGame.CoreCorners
