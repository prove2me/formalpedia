-- Prove2me | Theorems.Thm_ExecCompLP_Consistency_minimizer_stable
-- name    : ExecCompLP.Consistency.minimizer_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:26:01.879605+00:00
-- url     : https://prove2.me/theorems/8ec9a258-687f-4589-a650-f29bf89f4105
-- title:
--   §8, Proof, p. 151 — the gap argument: a unique nondegenerate optimum stays the unique optimum, and moves little, under small modification
-- statement:
--   Let $\xi$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose that
--
--   1. (Assumption (I)) the program (8) with matrix $\xi$ has a unique minimizing solution $\hat\alpha$;
--   2. $\hat\alpha$ is nondegenerate: the number of positive $\hat\alpha_j$ plus the number of constraints with $\sum_j\xi_{ij}\hat\alpha_j>b_i$ equals $m$.
--
--   Then for every $\varepsilon>0$ there is $\delta>0$ such that for every real $m\times n$ matrix $X$ with $|x_{ij}-\xi_{ij}|<\delta$ for all $i,j$, the program (8) with matrix $X$ has a unique minimizing solution $\hat a$, and
--
--   $$\max_j|\hat a_j-\hat\alpha_j|<\varepsilon.$$
--
--   This is the deterministic form of the comparison of values on p. 151: with $\gamma=c\tilde\alpha-c\hat\alpha>0$ for every other extreme point $\tilde\alpha$, small perturbations cannot change which extreme point is optimal. The consistency theorem follows from it, since the sampling errors are small with probability tending to one.
--
--   **Formalization Note** Assumption (II) of the paper is not a hypothesis here, as the argument does not use it; this makes the statement stronger. The nondegeneracy hypothesis is an addition to the paper, without which the statement is false (see the companion counterexample).
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 151, §8, Proof, from "Let γ ≡ cα̃ − cα̂" to "with minimal ca as required"

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

namespace ExecCompLP.Consistency

theorem minimizer_stable {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (αhat : Fin n → ℝ) (hI : AssumptionI ξ b c αhat)
    (hnd : Nondegenerate ξ b αhat) :
    ∀ ε > 0, ∃ δ > 0, ∀ X : Matrix (Fin m) (Fin n) ℝ, (∀ i j, |X i j - ξ i j| < δ) →
      ∃ a, IsMinimizer X b c a ∧ (∀ a', IsMinimizer X b c a' → a' = a) ∧
        dist a αhat < ε := by sorry

end ExecCompLP.Consistency
