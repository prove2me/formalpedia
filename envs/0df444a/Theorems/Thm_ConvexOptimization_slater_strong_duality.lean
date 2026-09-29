-- Prove2me | Theorems.Thm_ConvexOptimization_slater_strong_duality
-- name    : ConvexOptimization.slater_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:33:23.559837+00:00
-- url     : https://prove2.me/theorems/1554b0c4-ca13-4b43-bde7-74e0644e3be5
-- title:
--   Slater's theorem: strong duality with dual attainment
-- statement:
--   **Slater's theorem: strong duality with dual attainment.**
--
--   Consider the standard problem on $\mathbb{R}^n$ with objective $f_0$, inequality constraints $f_i(x) \le 0$ $(i = 1,\dots,m)$ and equality constraints $\langle a_j, x\rangle = b_j$ $(j = 1,\dots,p)$, and assume
--
--   * $f_0$ and every $f_i$ are convex on $\mathbb{R}^n$;
--   * the vectors $a_1,\dots,a_p$ are linearly independent (the full-rank condition on the equality constraints);
--   * **Slater's condition**: there is a point $\tilde{x}$ with $f_i(\tilde{x}) < 0$ for every $i$ and $\langle a_j,\tilde{x}\rangle = b_j$ for every $j$;
--   * the optimal value $p^{\star} = \inf\{f_0(x) : x \text{ feasible}\}$ is finite (the objective is bounded below on the feasible set).
--
--   Then the dual optimum is attained and the duality gap is zero: there exist $\lambda \in \mathbb{R}^m$ with $\lambda \succeq 0$ and $\nu \in \mathbb{R}^p$ such that
--
--   $$g(\lambda,\nu) \;=\; p^{\star} .$$
--
--   Strong duality is the deepest result of the chapter, and *attainment* is the part that matters here: the theorem does not merely close the gap in the limit, it produces an actual multiplier pair, and those multipliers are exactly the $\lambda^{\star},\nu^{\star}$ appearing in the KKT conditions. Slater's condition cannot simply be dropped — without an interior feasible point the gap can be strictly positive.
--
--   **Formalization Note** $p^{\star}$ appears as `sInf (f₀ '' feasibleSet fc a b)` and the boundedness hypothesis `BddBelow` is what makes that infimum meaningful rather than a junk value; the conclusion equates the `EReal`-valued dual function with the coercion of that real number, which also asserts finiteness of $g(\lambda,\nu)$. Source: B&V §5.3.2, pp. 234–236, the book's separating-hyperplane proof.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 234-236, §5.3.2 (Slater's condition; proof of strong duality via a separating hyperplane). Formalized with the hypotheses the book's proof actually uses: convex data total on R^n, linearly independent equality rows, and a finite optimal value

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.slater_strong_duality {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_ineq : ∀ i, fc i xs < 0)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' feasibleSet fc a b)) :
    ∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧
      dualFunction f₀ fc a b lam nu =
        ((sInf (f₀ '' feasibleSet fc a b) : ℝ) : EReal) := by
  sorry
