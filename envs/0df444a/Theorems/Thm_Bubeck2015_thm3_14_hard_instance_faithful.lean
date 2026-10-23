-- Prove2me | Theorems.Thm_Bubeck2015_thm3_14_hard_instance_faithful
-- name    : Bubeck2015.thm3_14_hard_instance_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T03:20:06.997801+00:00
-- url     : https://prove2.me/theorems/59ca9328-55e6-4930-a406-1171e9fa8eec
-- title:
--   Theorem 3.14 for the hard instance $f_{2t+1}$ (lower bound $\frac{3\beta}{32}\|x_1-x^*\|^2/(t+1)^2$)
-- statement:
--   Let $n,t$ be integers with $1\le t$ and $2t+1\le n$, and let $\beta>0$. Let $e_1,\dots,e_n$ be the canonical basis of $\mathbb R^n$, $A_k$ the symmetric tridiagonal matrix with $(A_k)_{i,i}=2$ for $i\le k$, $(A_k)_{i,j}=-1$ for $j\in\{i-1,i+1\}$, $i\le k$, $j\ne k+1$, and $0$ otherwise, $f_k(x)=\frac\beta8x^\top A_kx-\frac\beta4x^\top e_1$, and $x^*_k\in\mathbb R^n$ with $x^*_k(i)=1-\frac{i}{k+1}$ for $i\le k$ and $0$ otherwise. Then $f=f_{2t+1}$ is convex and $\beta$-smooth, $x^*=x^*_{2t+1}$ minimizes it, and every black-box procedure with $x_1=0$ and $x_{s+1}\in\mathrm{Span}(\nabla f(x_1),\dots,\nabla f(x_s))$ satisfies
--
--   $$\min_{1\le s\le t}f(x_s)-f(x^*)\ \ge\ \frac{3\beta}{32}\,\frac{\|x_1-x^*\|^2}{(t+1)^2}.$$
--
--   This is Theorem 3.14 of Bubeck (2015) with the function and the minimizer of the book's proof made explicit. The existing theorem ConvexOptAlg.LowerBounds.theorem_3_14 quantifies $f$ and $x^*$ existentially, which the zero function with $x^*=0$ satisfies trivially; here the instance is fixed, so the right side is $\frac{3\beta}{32}\|x^*_{2t+1}\|^2/(t+1)^2>0$ and the statement is the lower bound that makes Nesterov's rate optimal.
--
--   **Formalization Note** The gradient map $g$ is existentially quantified but is forced to be $\nabla f_{2t+1}$ by the gradient condition; $\beta$-smoothness means $g$ is $\beta$-Lipschitz. Coordinates are 1-based in the book and 0-based in Lean, as in the definitions file. The minimum over $1\le s\le t$ is stated as the bound for every such $s$.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Foundations and Trends in Machine Learning 8(3-4), 2015, doi:10.1561/2200000050 (arXiv:1405.4980v2), Theorem 3.14, p. 282, with the instance of its proof, pp. 282–283

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace
open ConvexOptAlg.LowerBounds

theorem Bubeck2015.thm3_14_hard_instance_faithful (n t : ℕ) (β : ℝ) (ht : 1 ≤ t)
    (htn : 2 * t + 1 ≤ n) (hβ : 0 < β) :
    ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ y, HasGradientAt (fK n β (2 * t + 1)) (g y) y) ∧ IsBetaSmooth g β ∧
        ConvexOn ℝ Set.univ (fK n β (2 * t + 1)) ∧
        (∀ y, fK n β (2 * t + 1) (xstarK n (2 * t + 1)) ≤ fK n β (2 * t + 1) y) ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), SatisfiesSpanCondition g x →
          ∀ s ∈ Finset.Icc 1 t,
            fK n β (2 * t + 1) (x s) - fK n β (2 * t + 1) (xstarK n (2 * t + 1)) ≥
              3 * β / 32 * (‖x 1 - xstarK n (2 * t + 1)‖ ^ 2 / ((t : ℝ) + 1) ^ 2) := by sorry
