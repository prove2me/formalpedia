-- Prove2me | Theorems.Thm_AssignmentGame_CoreLP_core_eq_dual_optimal
-- name    : AssignmentGame.CoreLP.core_eq_dual_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:17:05.043831+00:00
-- url     : https://prove2.me/theorems/c4adce45-0395-46ce-b5cb-e9354720905e
-- title:
--   Theorem 2 — the core of an assignment game is the set of optimal solutions of the dual assignment LP
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and $a = (a_{ij})_{i\in M, j \in N}$ a matrix with $a_{ij} \ge 0$. The core of the assignment game — the set of payoff vectors $(u, v) \in \mathbb R^M \times \mathbb R^N$ with
--   $$\sum_{i \in M} u_i + \sum_{j \in N} v_j = v(M \cup N), \qquad \sum_{i \in S\cap M} u_i + \sum_{j \in S \cap N} v_j \ge v(S) \text{ for every coalition } S,$$
--   where $v$ is the characteristic function (2.6) — is exactly the set of optimal solutions of the dual LP
--   $$\min \sum_{i \in M} u_i + \sum_{j \in N} v_j \quad\text{subject to}\quad u_i \ge 0,\ v_j \ge 0,\ u_i + v_j \ge a_{ij}\ (i \in M, j \in N).$$
--
--   The theorem identifies a cooperative solution concept, defined by exponentially many coalition constraints, with the optimal face of a linear program with $|M|\cdot|N|$ constraints; existence of the core and its computation follow.
--
--   **Formalization Note** "Solutions of the LP dual" is read as *optimal* solutions, as the surrounding text on p. 118 does ("a vector that minimizes (3.4), subject to (3.3)"). The core and the dual are defined independently in `Def_AssignmentGame_CoreLP_Game`; the statement is a set equality in `(M → ℝ) × (N → ℝ)`.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 118, Theorem 2

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

open Finset

namespace AssignmentGame.CoreLP

theorem core_eq_dual_optimal {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    core a = {p : (M → ℝ) × (N → ℝ) | DualOptimal a p} := by sorry

end AssignmentGame.CoreLP
