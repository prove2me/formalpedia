-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_unbounded_of_neg_cost
-- name    : ChinesePostman.Polyhedron.unbounded_of_neg_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:02.595988+00:00
-- url     : https://prove2.me/theorems/bf168d06-5da8-48b4-a027-0fc820301f6f
-- title:
--   §3, p. 96 — if some c_e < 0, z is unbounded below over both the polyhedron and the parity points
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops), $c\in\mathbb R^E$, and suppose $c_{e_0}<0$ for some edge $e_0$. Write $\mathbf 1_{e_0}$ for the unit vector of $e_0$ and $z(x)=\sum_e c_e x_e$. Then for every real $M$:
--
--   1. for every point $x$ of the postman polyhedron ((3.2), (3.5)) there is $t\ge 0$ such that $x+t\,\mathbf 1_{e_0}$ is still in the polyhedron and $z(x+t\,\mathbf 1_{e_0})<M$;
--   2. for every parity point $x$ ((3.1), (3.2), (3.6)) there is a positive integer $k$ such that $x+2k\,\mathbf 1_{e_0}$ is still a parity point and $z(x+2k\,\mathbf 1_{e_0})<M$.
--
--   So for an objective with a negative coefficient both the linear program and the parity problem are unbounded, which is why only $c\ge 0$ matters for comparing the two sets.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 96, §3

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem unbounded_of_neg_cost {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (e₀ : E) (h : c e₀ < 0) :
    (∀ x ∈ postmanPolyhedron G, ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧
        x + t • Pi.single e₀ 1 ∈ postmanPolyhedron G ∧
        objective c (x + t • Pi.single e₀ 1) < M) ∧
      (∀ x ∈ parityPoints G, ∀ M : ℝ, ∃ k : ℕ, 0 < k ∧
        x + (2 * k : ℝ) • Pi.single e₀ 1 ∈ parityPoints G ∧
        objective c (x + (2 * k : ℝ) • Pi.single e₀ 1) < M) := by sorry

end ChinesePostman.Polyhedron
