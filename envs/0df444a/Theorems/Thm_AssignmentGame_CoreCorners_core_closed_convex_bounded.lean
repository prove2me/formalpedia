-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_closed_convex_bounded
-- name    : AssignmentGame.CoreCorners.core_closed_convex_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:23:07.401933+00:00
-- url     : https://prove2.me/theorems/d5c84577-a42b-4c71-bf68-8d115b5ea41a
-- title:
--   Sec. 3.3 — the core is a closed, convex, bounded (polyhedral) set
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and $a_{ij} \ge 0$ for all $i \in M$, $j \in N$. The core of the assignment game, viewed as a subset of $\mathbb{R}^M \times \mathbb{R}^N$, is
--
--   1. closed,
--   2. convex, and
--   3. bounded.
--
--   The paper describes the core as "a closed, convex polyhedral set" (Sec. 3.3, p. 120). It is cut out by finitely many linear equations and inequalities, and it lies in the box $0 \le u_i, v_j \le \operatorname{worth}(M, N)$, so the polyhedron is a polytope. Boundedness and closedness are what guarantee that the highest and lowest core payoffs of Theorem 3 are finite and attained.
--
--   **Formalization Note** "Polyhedral" is rendered by its three topological/convex consequences used in the paper (closed, convex, bounded); the informal dimension statements of the same paragraph are not formalized. Boundedness is with respect to the product metric of $\mathbb{R}^M \times \mathbb{R}^N$; all norms on this finite-dimensional space give the same bounded sets.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 120, Sec. 3.3

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open Finset

namespace AssignmentGame.CoreCorners

/-- Sec. 3.3, p. 120: the core is a closed, convex and bounded (polyhedral) subset of
`ℝ^M × ℝ^N`. -/
theorem core_closed_convex_bounded {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    IsClosed (core a) ∧ Convex ℝ (core a) ∧ Bornology.IsBounded (core a) := by sorry

end AssignmentGame.CoreCorners
