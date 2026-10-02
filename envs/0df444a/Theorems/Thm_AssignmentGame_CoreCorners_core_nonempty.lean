-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_nonempty
-- name    : AssignmentGame.CoreCorners.core_nonempty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:22:24.731646+00:00
-- url     : https://prove2.me/theorems/20861a62-09ba-46b1-8ae6-02092deafbc3
-- title:
--   Sec. 3.2 — the core of an assignment game is nonempty
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and let $a = (a_{ij})$ be a matrix with $a_{ij} \ge 0$ for all $i \in M$, $j \in N$. Then the core of the assignment game with characteristic function (2.6) is nonempty: there is a payoff vector $(u, v) \in \mathbb{R}^M \times \mathbb{R}^N$ with
--   $$\sum_{i \in M} u_i + \sum_{j \in N} v_j = \operatorname{worth}(M, N), \qquad \sum_{i \in A} u_i + \sum_{j \in B} v_j \ge \operatorname{worth}(A, B) \ \text{ for all } A \subseteq M,\ B \subseteq N.$$
--
--   In the paper this is the first consequence of Theorem 2 (the core is the set of optimal solutions of the dual assignment LP) drawn in Sec. 3.2. Here it is needed because the extremal payoffs $u^*_i, u_{*i}, v^*_j, v_{*j}$ of Theorem 3 are defined over the core.
--
--   **Formalization Note** No hypothesis that $M$ or $N$ is nonempty is made; if one of them is empty the core is $\{(0, 0)\}$.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 118, Sec. 3.2 (existence of the core, from Theorem 2)

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open Finset

namespace AssignmentGame.CoreCorners

/-- Sec. 3.2, p. 118: the core of an assignment game with nonnegative matrix `a` is nonempty. -/
theorem core_nonempty {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (core a).Nonempty := by sorry

end AssignmentGame.CoreCorners
