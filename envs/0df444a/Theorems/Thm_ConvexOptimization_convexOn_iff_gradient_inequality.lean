-- Prove2me | Theorems.Thm_ConvexOptimization_convexOn_iff_gradient_inequality
-- name    : ConvexOptimization.convexOn_iff_gradient_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:39:55.972578+00:00
-- url     : https://prove2.me/theorems/a0deca2b-0dec-4c42-9af1-e1c335ffdd33
-- title:
--   First-order characterization of convexity
-- statement:
--   **First-order characterization of convexity:** a differentiable function is convex exactly when its tangent planes lie below its graph.
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and convex, and let $f$ be differentiable on $\Omega$ with gradient field $\nabla f$. Then
--
--   $$f \text{ is convex on } \Omega \qquad\Longleftrightarrow\qquad f(y) \;\ge\; f(x) + \langle \nabla f(x),\, y - x\rangle \quad \text{for all } x, y \in \Omega .$$
--
--   The right-hand condition says that the first-order Taylor approximation at any point is a *global* underestimator of $f$ on $\Omega$ — a remarkable amount of global information extracted from a derivative at a single point.
--
--   This is the workhorse of the theory: it yields the first-order optimality criterion, the definition of the subgradient in the nondifferentiable case, and the strong-convexity inequality $f(y) \ge f(x) + \langle\nabla f(x), y-x\rangle + \tfrac{m}{2}\lVert y-x\rVert^2$ that drives all convergence-rate analysis.
--
--   **Formalization Note** The gradient is an explicit field `f'` tied to `f` by `∀ x ∈ Ω, HasGradientAt f (f' x) x`; openness of `Ω` is assumed so that the derivative is a genuine (two-sided) gradient at every point of the domain, and convexity of `Ω` is assumed separately from `ConvexOn ℝ Ω f`. Source: B&V §3.1.3, pp. 69–70.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 69-70, §3.1.3 eq. (3.2) (first-order condition for convexity)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.convexOn_iff_gradient_inequality {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x ∈ Ω, HasGradientAt f (f' x) x) :
    ConvexOn ℝ Ω f ↔ ∀ x ∈ Ω, ∀ y ∈ Ω, f x + ⟪f' x, y - x⟫ ≤ f y := by
  sorry
