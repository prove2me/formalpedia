-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_Supplement_theorem_a_basic_feasible
-- name    : DantzigSimplex.Technique.Supplement.theorem_a_basic_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:05:21.526612+00:00
-- url     : https://prove2.me/theorems/80f12837-8739-45bd-8565-f7d3de113ffa
-- title:
--   Theorem A — a feasible problem has a basic feasible solution (at most m positive weights)
-- statement:
--   Consider Dantzig's equality-form problem: columns $P_1,\ldots,P_n\in\mathbb R^m$, a right-hand side $P_0\in\mathbb R^m$ and costs $c_1,\ldots,c_n$. A **feasible solution** is a weight vector $\lambda\in\mathbb R^n$ with
--   $$
--   \lambda_j\ge 0\quad(j=1,\ldots,n),\qquad \sum_{j=1}^n \lambda_j P_j = P_0 .
--   $$
--   **Theorem A.** If one feasible solution exists, then there is a feasible solution $\lambda$ (a **basic feasible solution**) with at most $m$ positive weights and at least $n-m$ zero weights:
--   $$
--   \#\{j:\lambda_j>0\}\le m,\qquad \#\{j:\lambda_j=0\}\ \ge\ n-m .
--   $$
--   No nondegeneracy, rank or dimension condition is assumed: the paper notes that the proofs of Theorems A and B do not require the nondegeneracy assumption. The result is a companion theorem of the mission; it is not a step in the proof of the goal theorem.
--
--   **Formalization Note** The problem data and feasibility are the published base definitions `Problem` and `Problem.Feasible`. Indices run over `Fin n` and `Fin m`; all data are real. The lower bound $n-m$ is computed in $\mathbb Z$, so it is vacuous when $n<m$, as in the source.
--
--   Differences from the source: none.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, p. 341, Theorem A

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Problem

namespace DantzigSimplex.Technique.Supplement
open DantzigSimplex.Technique

theorem theorem_a_basic_feasible {m n : ℕ} (p : Problem m n)
    (hfeas : ∃ w : Fin n → ℝ, p.Feasible w) :
    ∃ w : Fin n → ℝ, p.Feasible w ∧
      (Finset.univ.filter (fun j => 0 < w j)).card ≤ m ∧
      (n : ℤ) - (m : ℤ) ≤ ((Finset.univ.filter (fun j => w j = 0)).card : ℤ) := by sorry

end DantzigSimplex.Technique.Supplement
