-- Prove2me | Theorems.Thm_ErrBoundQG_Structured_eq_4_3
-- name    : ErrBoundQG.Structured.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:12.991561+00:00
-- url     : https://prove2.me/theorems/2013c4e0-a248-4ddd-8114-566197309301
-- title:
--   Equation (4.3), p. 10 — relative interiors under dual strict complementarity
-- statement:
--   Under the structured convex model, dual nondegeneracy, and dual strict complementarity at a dual minimizer $\bar y$, write $F=\partial f^*(\bar y)$ and $G=\partial g^*(-A^\top\bar y)$. Then
--
--   $$0\in\operatorname{ri}\partial\Psi(\bar y)=\operatorname{ri}(F-AG)=\operatorname{ri}F-A(\operatorname{ri}G).$$
--
--   The relative-interior identity is the regularity input used to compare distance to the intersection with distances to its two factors.
--
--   **Formalization Note.** Subtraction of sets denotes pointwise Minkowski subtraction, and $A(G)$ is the image of $G$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 10, (4.3)

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

namespace ErrBoundQG.Structured

open scoped Pointwise

/-- Relative-interior identity (4.3), §4, p. 10. -/
theorem eq_4_3 {m n : ℕ}
    (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hnd : DualNondegenerate f g A)
    (hsc : DualStrictComplementarity f g A ybar) :
    let F := ProxAlg.FixedPoint.subdifferential
      (conj (fun z => (f z : EReal))) ybar
    let G := ProxAlg.FixedPoint.subdifferential
      (conj g) (-(ContinuousLinearMap.adjoint A ybar))
    (0 : E m) ∈ intrinsicInterior ℝ (ProxAlg.FixedPoint.subdifferential
      (dualObj f g A) ybar) ∧
    intrinsicInterior ℝ (ProxAlg.FixedPoint.subdifferential
      (dualObj f g A) ybar) = intrinsicInterior ℝ (F + -(A '' G)) ∧
    intrinsicInterior ℝ (F + -(A '' G)) =
      intrinsicInterior ℝ F + -(A '' intrinsicInterior ℝ G) := by sorry

end ErrBoundQG.Structured
