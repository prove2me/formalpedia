-- Prove2me | Theorems.Thm_AssignmentGame_CoreLP_coalition_rational_of_dual_feasible
-- name    : AssignmentGame.CoreLP.coalition_rational_of_dual_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:12:00.142985+00:00
-- url     : https://prove2.me/theorems/aa5f6dab-8b89-4028-8407-dad56169172a
-- title:
--   Eq. (3.6) — a dual-feasible payoff vector gives every coalition at least its worth
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and $a = (a_{ij})$ a matrix with $a_{ij} \ge 0$. Let $(u, v)$ be a feasible solution of the dual assignment LP, i.e. $u_i \ge 0$, $v_j \ge 0$ and $u_i + v_j \ge a_{ij}$ for all $i \in M$, $j \in N$. Then for every coalition $S$, with sellers $A = S \cap M$ and buyers $B = S \cap N$,
--   $$\sum_{i \in A} u_i + \sum_{j \in B} v_j \ \ge\ v(S),$$
--   where $v(S)$ is the characteristic function (2.6), the maximum of $\sum_{(i,j)\in P} a_{ij}$ over matchings $P$ inside the coalition.
--
--   This is the coalitional-rationality half of the statement that dual solutions lie in the core.
--
--   **Formalization Note** The coalition is the pair of finite sets $(A, B)$; $A$ and $B$ may be empty.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 118, Eq. (3.6)

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

open Finset

namespace AssignmentGame.CoreLP

theorem coalition_rational_of_dual_feasible {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) (p : (M → ℝ) × (N → ℝ))
    (hp : DualFeasible a p) (A : Finset M) (B : Finset N) :
    worth a A B ≤ ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j := by sorry

end AssignmentGame.CoreLP
