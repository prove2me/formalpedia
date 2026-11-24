-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_Supplement_theorem_b_maximum_basic
-- name    : DantzigSimplex.Technique.Supplement.theorem_b_maximum_basic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:05:54.285231+00:00
-- url     : https://prove2.me/theorems/12785fbe-23a7-4ff7-8b09-36dae649863a
-- title:
--   Theorem B (corrected: assumes a feasible solution exists) — bounded objective gives a basic maximum feasible solution
-- statement:
--   Consider Dantzig's equality-form problem: columns $P_1,\ldots,P_n\in\mathbb R^m$, a right-hand side $P_0\in\mathbb R^m$ and costs $c_1,\ldots,c_n$, with objective $z(\lambda)=\sum_j \lambda_j c_j$. A **feasible solution** is $\lambda\in\mathbb R^n$ with $\lambda_j\ge0$ for all $j$ and $\sum_j\lambda_jP_j=P_0$; a **maximum feasible solution** is a feasible $\lambda^*$ with $z(\lambda)\le z(\lambda^*)$ for every feasible $\lambda$.
--
--   **Theorem B.** Assume that a feasible solution exists and that the values of $z$ on the feasible solutions have a finite upper bound $U\in\mathbb R$. Then there is a maximum feasible solution $\lambda^*$ which is basic:
--   $$
--   \#\{j:\lambda^*_j>0\}\le m,\qquad \#\{j:\lambda^*_j=0\}\ \ge\ n-m .
--   $$
--   No nondegeneracy, rank or dimension condition is assumed (the paper states that the proofs of Theorems A and B do not require nondegeneracy). The result is a companion theorem of the mission; it is not a step in the proof of the goal theorem.
--
--   **Formalization Note** The data, feasibility and maximum feasible solution are the published base definitions `Problem`, `Problem.Feasible` and `Problem.MaximumFeasible`. The lower bound $n-m$ is computed in $\mathbb Z$, so it is vacuous when $n<m$.
--
--   Differences from the source:
--   - correction: the printed theorem assumes only a finite upper bound for $z$ on the feasible class → the Lean statement also assumes that a feasible solution exists; reason: an empty feasible class is bounded above but has no maximum (for $m=n=1$, $P_1=1$, $P_0=-1$, $c_1=0$); Section 1 on the same page starts from a given feasible solution. Excluded cases: infeasible problems only.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, p. 341, Theorem B

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Problem

namespace DantzigSimplex.Technique.Supplement
open DantzigSimplex.Technique

theorem theorem_b_maximum_basic {m n : ℕ} (p : Problem m n)
    (hfeas : ∃ w : Fin n → ℝ, p.Feasible w)
    (hbdd : ∃ U : ℝ, ∀ w : Fin n → ℝ, p.Feasible w → p.objective w ≤ U) :
    ∃ w : Fin n → ℝ, p.MaximumFeasible w ∧
      (Finset.univ.filter (fun j => 0 < w j)).card ≤ m ∧
      (n : ℤ) - (m : ℤ) ≤ ((Finset.univ.filter (fun j => w j = 0)).card : ℤ) := by sorry

end DantzigSimplex.Technique.Supplement
