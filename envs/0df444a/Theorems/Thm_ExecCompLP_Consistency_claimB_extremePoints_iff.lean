-- Prove2me | Theorems.Thm_ExecCompLP_Consistency_claimB_extremePoints_iff
-- name    : ExecCompLP.Consistency.claimB_extremePoints_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:25:37.750917+00:00
-- url     : https://prove2.me/theorems/f7e8ca04-b1d7-4860-a30f-383948687a8b
-- title:
--   §8, Proof, claim B, p. 150 — extreme points of the solution set are the points whose positive columns are linearly independent
-- statement:
--   Let $X=(x_{ij})$ be a real $m\times n$ matrix and $b\in\mathbb R^m$, and let $F=\{a\in\mathbb R^n: a\ge 0,\ \sum_j x_{ij}a_j\ge b_i\ \forall i\}$ be the feasible set of (8). Introduce the surplus $s_i=\sum_j x_{ij}a_j-b_i$, so that (8) reads $[X,\,-I]\binom{a}{s}=b$, $a,s\ge 0$. For a point $a\in\mathbb R^n$ the following are equivalent:
--
--   $$a \text{ is an extreme point of } F \iff a\in F \text{ and the columns of } [X,\,-I] \text{ at which } (a,s) \text{ is strictly positive are linearly independent}.$$
--
--   Here the column of the variable $j$ is the $j$-th column of $X$, used when $a_j>0$, and the column of the surplus variable $i$ is $-e_i$, used when $s_i>0$.
--
--   This is claim B of the proof in §8: "the extreme points of the convex set of solutions come precisely from the linearly independent sets of columns which have positive elements". It is the inequality-form version of the classical characterization of basic feasible solutions, and it is what lets claim A transfer extreme points of the true set to the sample set.
--
--   **Formalization Note** The paper does not say how surplus variables enter; reading claim B in the inequality form (8) requires the surplus columns $-e_i$, as stated here. The parenthetical of claim B ("This property is likewise preserved under sufficiently small modifications") is not part of this item: it fails at degenerate extreme points (see the companion counterexample).
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 150, §8, Proof, claim B

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

namespace ExecCompLP.Consistency

theorem claimB_extremePoints_iff {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (a : Fin n → ℝ) :
    a ∈ Set.extremePoints ℝ (feasibleSet X b) ↔
      a ∈ feasibleSet X b ∧
        LinearIndependent ℝ (fun k : {k // posSupp X b a k} => augCol X k.1) := by sorry

end ExecCompLP.Consistency
