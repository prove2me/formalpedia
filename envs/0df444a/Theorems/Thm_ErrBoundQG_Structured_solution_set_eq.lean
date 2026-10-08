-- Prove2me | Theorems.Thm_ErrBoundQG_Structured_solution_set_eq
-- name    : ErrBoundQG.Structured.solution_set_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:53.003364+00:00
-- url     : https://prove2.me/theorems/eb82323d-19ca-4f40-9692-d6457bcb0fc6
-- title:
--   §4, p. 10 — Kuhn–Tucker description of the primal solution set
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be convex and continuously differentiable, let $g:\mathbb R^n\to(-\infty,+\infty]$ be proper, closed, and convex, and let $A:\mathbb R^n\to\mathbb R^m$ be linear. Suppose the primal problem has a nonempty solution set $S$, $\bar y$ minimizes the dual objective $\Psi(y)=f^*(y)+g^*(-A^\top y)$, and dual nondegeneracy holds. Then
--
--   $$S=\partial g^*(-A^\top\bar y)\cap A^{-1}\bigl(\partial f^*(\bar y)\bigr).$$
--
--   This identifies primal minimizers through two dual subdifferentials and underlies the regularity estimate (4.4).
--
--   **Formalization Note.** The set $S$ is pinned to the exact minimizer set by an equality binder. The conjugate uses the Euclidean inner product.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 10, §4 after (4.3)

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

namespace ErrBoundQG.Structured

open scoped Pointwise

/-- KKT description of the primal solution set, §4, p. 10. -/
theorem solution_set_eq {m n : ℕ}
    (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hnd : DualNondegenerate f g A) :
    S = ProxAlg.FixedPoint.subdifferential (conj g)
          (-(ContinuousLinearMap.adjoint A ybar)) ∩
        A ⁻¹' ProxAlg.FixedPoint.subdifferential
          (conj (fun z => (f z : EReal))) ybar := by sorry

end ErrBoundQG.Structured
