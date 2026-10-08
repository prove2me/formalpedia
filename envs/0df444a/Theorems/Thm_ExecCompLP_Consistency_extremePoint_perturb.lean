-- Prove2me | Theorems.Thm_ExecCompLP_Consistency_extremePoint_perturb
-- name    : ExecCompLP.Consistency.extremePoint_perturb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:25:58.230025+00:00
-- url     : https://prove2.me/theorems/5ec73f5a-37f7-4b97-88a1-6e179b1d3009
-- title:
--   §8, Proof, p. 150 — a nondegenerate extreme point has a corresponding nearby extreme point under small modification of the data
-- statement:
--   Let $\xi$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, and let $\alpha$ be an extreme point of the feasible set $F(\xi,b)$ of (8) which is nondegenerate: the number of indices $j$ with $\alpha_j>0$ plus the number of constraints $i$ with $\sum_j\xi_{ij}\alpha_j>b_i$ equals $m$. Then for every $\varepsilon>0$ there is $\delta>0$ such that every real $m\times n$ matrix $X$ with $|x_{ij}-\xi_{ij}|<\delta$ for all $i,j$ has an extreme point $a$ of $F(X,b)$ with
--
--   $$\operatorname{supp}^+_{X}(a)=\operatorname{supp}^+_{\xi}(\alpha)\qquad\text{and}\qquad \max_j|a_j-\alpha_j|<\varepsilon,$$
--
--   where $\operatorname{supp}^+$ denotes the set of strictly positive variables and strictly positive surpluses.
--
--   This is the deterministic content of the sentence "as $N\to\infty$ these extreme points respectively approach the extreme points of the true set in probability" of the proof in §8, for a nondegenerate extreme point. The equality of positive supports makes $a$ the *corresponding* extreme point of $\alpha$ in the sense of the paper.
--
--   **Formalization Note** The paper states this for every extreme point; it fails at degenerate extreme points (the sample set may lose the point, or be empty), so the item carries the nondegeneracy hypothesis. The randomness of the paper is removed: the statement is about all matrices within $\delta$ of $\xi$ entrywise; distances between points use the maximum norm.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 150, §8, Proof, paragraph after claim B

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

namespace ExecCompLP.Consistency

theorem extremePoint_perturb {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (α : Fin n → ℝ) (hα : α ∈ Set.extremePoints ℝ (feasibleSet ξ b))
    (hnd : Nondegenerate ξ b α) :
    ∀ ε > 0, ∃ δ > 0, ∀ X : Matrix (Fin m) (Fin n) ℝ, (∀ i j, |X i j - ξ i j| < δ) →
      ∃ a ∈ Set.extremePoints ℝ (feasibleSet X b),
        posSupp X b a = posSupp ξ b α ∧ dist a α < ε := by sorry

end ExecCompLP.Consistency
