-- Prove2me | Theorems.Thm_ConvexOptimization_kkt_iff_optimal_slater
-- name    : ConvexOptimization.kkt_iff_optimal_slater
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:36:16.018741+00:00
-- url     : https://prove2.me/theorems/cd4162d1-fdfa-4552-ad6f-14220e29a523
-- title:
--   KKT conditions characterize optimality under Slater's condition
-- statement:
--   **The KKT conditions characterize optimality for convex problems satisfying Slater's condition** — the goal of this mission.
--
--   Consider the standard problem on $\mathbb{R}^n$,
--
--   $$\text{minimize } f_0(x) \quad \text{subject to } f_i(x) \le 0 \ (i = 1,\dots,m), \quad \langle a_j, x\rangle = b_j \ (j = 1,\dots,p),$$
--
--   and assume: $f_0$ and every $f_i$ are convex and differentiable, with gradient fields $\nabla f_0$, $\nabla f_i$; the vectors $a_1,\dots,a_p$ are linearly independent; and Slater's condition holds — some $\tilde{x}$ satisfies $f_i(\tilde{x}) < 0$ for all $i$ and $\langle a_j, \tilde{x}\rangle = b_j$ for all $j$. Then for any point $x^{\star}$,
--
--   $$x^{\star} \text{ is feasible and minimizes } f_0 \text{ over the feasible set} \iff \exists\, \lambda \in \mathbb{R}^m,\ \nu \in \mathbb{R}^p \text{ with } (x^{\star},\lambda,\nu) \text{ a KKT point},$$
--
--   where being a KKT point means $f_i(x^{\star}) \le 0$, $\langle a_j,x^{\star}\rangle = b_j$, $\lambda \succeq 0$, $\lambda_i f_i(x^{\star}) = 0$ and $\nabla f_0(x^{\star}) + \sum_i \lambda_i\nabla f_i(x^{\star}) + \sum_j \nu_j a_j = 0$.
--
--   This is the theorem that makes the KKT system the working definition of optimality in convex optimization: the conditions are not merely necessary, and not merely sufficient, but an exact characterization. Sufficiency holds for any convex problem; necessity is where Slater's condition is used, via strong duality with attained dual optimum. Almost every algorithm and every hand derivation in the field is an attempt to solve this system.
--
--   **Formalization Note** The right-hand side uses the mission's `IsKKTPoint` predicate; optimality is `IsMinOn f₀ (feasibleSet fc a b) x⋆` and convexity is asserted on `Set.univ`, matching the total-function form of the problem. Slater's point and the independence of the `a j` appear as explicit hypotheses of the whole iff, so both directions are stated under them even though sufficiency does not need them. Source: B&V §5.5.3, p. 244, conditions (5.49).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 244, §5.5.3 eq. (5.49) (for a convex problem satisfying Slater's condition the KKT conditions are necessary and sufficient for optimality)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality
import Definitions.Def_ConvexOptimization_IsKKTPoint

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.kkt_iff_optimal_slater {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (f₀' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf₀' : ∀ x, HasGradientAt f₀ (f₀' x) x)
    (fc' : Fin mm → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfc' : ∀ i x, HasGradientAt (fc i) (fc' i x) x)
    (xsl : EuclideanSpace ℝ (Fin n)) (hxsl_ineq : ∀ i, fc i xsl < 0)
    (hxsl_eq : ∀ j, ⟪a j, xsl⟫ = b j)
    (xs : EuclideanSpace ℝ (Fin n)) :
    (xs ∈ feasibleSet fc a b ∧ IsMinOn f₀ (feasibleSet fc a b) xs) ↔
      ∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ),
        IsKKTPoint fc a b f₀' fc' xs lam nu := by
  sorry
