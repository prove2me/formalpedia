-- Prove2me | Theorems.Thm_ErrBoundQG_Structured_eq_4_4
-- name    : ErrBoundQG.Structured.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:55.907388+00:00
-- url     : https://prove2.me/theorems/7d2230f5-4715-443b-a85b-dc7eedb52c98
-- title:
--   Equation (4.4), p. 10 — compact-set linear regularity
-- statement:
--   In the setting of the structured convex problem, suppose dual nondegeneracy and strict complementarity hold. For every compact set $\mathcal X\subset\mathbb R^n$ there is $\kappa\ge0$ such that
--
--   $$\operatorname{dist}(x,S)\le\kappa\left[\operatorname{dist}\bigl(x,\partial g^*(-A^\top\bar y)\bigr)+\operatorname{dist}\bigl(Ax,\partial f^*(\bar y)\bigr)\right] \quad(x\in\mathcal X).$$
--
--   This linear regularity inequality combines the two dual factors into a bound on distance to primal solutions.
--
--   **Formalization Note.** The minimizer set is nonempty, and the factors are nonempty under the Kuhn–Tucker description; real `Metric.infDist` therefore represents the paper's distances on the hypotheses of this theorem.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 10, (4.4)

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

namespace ErrBoundQG.Structured

/-- Linear regularity (4.4), §4, p. 10. -/
theorem eq_4_4 {m n : ℕ}
    (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hnd : DualNondegenerate f g A)
    (hsc : DualStrictComplementarity f g A ybar) :
    ∀ X : Set (E n), IsCompact X →
      ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x ∈ X,
        Metric.infDist x S ≤ κ *
          (Metric.infDist x (ProxAlg.FixedPoint.subdifferential
            (conj g) (-(ContinuousLinearMap.adjoint A ybar))) +
           Metric.infDist (A x) (ProxAlg.FixedPoint.subdifferential
            (conj (fun z => (f z : EReal))) ybar)) := by sorry

end ErrBoundQG.Structured
