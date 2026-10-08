-- Prove2me | Theorems.Thm_ExecCompLP_Consistency_claimA_linearIndependent_perturb
-- name    : ExecCompLP.Consistency.claimA_linearIndependent_perturb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:25:29.62015+00:00
-- url     : https://prove2.me/theorems/08f736e4-d003-4c8d-b456-5f47aac35435
-- title:
--   §8, Proof, claim A, p. 150 — linear independence of columns survives sufficiently small modification
-- statement:
--   Let $\xi=(\xi_{ij})$ be a real $m\times n$ matrix and $S\subseteq\{1,\dots,n\}$ a set of column indices such that the columns $(\xi_{\cdot j})_{j\in S}$ are linearly independent in $\mathbb R^m$. Then there is $\delta>0$ such that for every real $m\times n$ matrix $X=(x_{ij})$ with
--
--   $$|x_{ij}-\xi_{ij}|<\delta\quad\text{for all } i,j,$$
--
--   the columns $(x_{\cdot j})_{j\in S}$ are again linearly independent.
--
--   This is claim A of the proof of consistency in §8: linear independence of a set of columns is an open condition on the entries of the matrix. It guarantees that a basis of the true program remains a basis of the sample program once the sampling errors are small.
--
--   **Formalization Note** Closeness of matrices is entrywise, since the paper names no norm; all norms on $\mathbb R^{m\times n}$ give the same statement.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 150, §8, Proof, claim A

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

namespace ExecCompLP.Consistency

theorem claimA_linearIndependent_perturb {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) (hS : LinearIndependent ℝ (fun j : S => fun i => ξ i j)) :
    ∃ δ > 0, ∀ X : Matrix (Fin m) (Fin n) ℝ, (∀ i j, |X i j - ξ i j| < δ) →
      LinearIndependent ℝ (fun j : S => fun i => X i j) := by sorry

end ExecCompLP.Consistency
