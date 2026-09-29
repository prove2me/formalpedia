-- Prove2me | Theorems.Thm_ConvexOptimization_log_barrier_affine_self_concordant
-- name    : ConvexOptimization.log_barrier_affine_self_concordant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:13:35.1212+00:00
-- url     : https://prove2.me/theorems/fe9e67b1-1ca9-4ef8-9233-f4e023f4db43
-- title:
--   The affine log barrier is self-concordant
-- statement:
--   **The logarithmic barrier of a polyhedron is self-concordant** — example 9.6 of Boyd & Vandenberghe.
--
--   Let $a_1,\dots,a_m \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$, and consider the open polyhedron $\Omega = \{x : \langle a_i, x\rangle < b_i \text{ for all } i\}$. Then
--
--   $$\varphi(x) \;=\; -\sum_{i=1}^{m} \log\bigl(b_i - \langle a_i, x\rangle\bigr)$$
--
--   is self-concordant on $\Omega$.
--
--   This is the concrete anchor of the abstract theory: every line restriction of $\varphi$ is a sum of terms $-\log(\text{affine})$, each of which meets the defining inequality with equality, and the closure of self-concordance under sums does the rest. It supplies the self-concordance hypothesis for linear and quadratic programming barriers, and hence for the complexity theorem that is the goal of this mission.
--
--   **Formalization Note** The domain is written as the set-builder `{x | ∀ i, ⟪a i, x⟫ < b i}` and the barrier is spelled out rather than routed through the mission's `logBarrier` definition, so that the constraint functions appear in the affine form $\langle a_i,x\rangle - b_i$ used in the book's example. Source: B&V §9.6.1, example 9.6, p. 497.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 499, §9.6.1 example 9.4 (log barrier for linear inequalities is self-concordant)

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.log_barrier_affine_self_concordant {n mI : ℕ}
    (a : Fin mI → EuclideanSpace ℝ (Fin n)) (b : Fin mI → ℝ) :
    IsSelfConcordantOn {x | ∀ i, ⟪a i, x⟫ < b i}
      (fun x => -∑ i, Real.log (b i - ⟪a i, x⟫)) := by
  sorry
