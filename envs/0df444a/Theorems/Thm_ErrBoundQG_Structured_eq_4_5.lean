-- Prove2me | Theorems.Thm_ErrBoundQG_Structured_eq_4_5
-- name    : ErrBoundQG.Structured.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:05.095186+00:00
-- url     : https://prove2.me/theorems/04cf4ce1-d44d-4304-9544-f6872d0c9582
-- title:
--   Equation (4.5), p. 11 — component quadratic-growth estimates
-- statement:
--   Let $\varphi(x)=f(Ax)+g(x)$ have a nonempty bounded minimizer set $S$, and let $\bar y$ be a dual minimizer under dual nondegeneracy and strict complementarity. Suppose $f$ and $g$ are firmly convex relative to $\bar y$ and $-A^\top\bar y$. Fix $\nu>0$, $\bar x\in S$, $\mathcal X=\{x:\varphi(x)\le\varphi^*+\nu\}$, and $\mathcal Y=A(\mathcal X)$. There are $c,\alpha>0$ for which
--
--   $$f(y)\ge f(A\bar x)+\langle\bar y,y-A\bar x\rangle+\frac c2\operatorname{dist}^2\bigl(y,(\partial f)^{-1}(\bar y)\bigr)\quad(y\in\mathcal Y),$$
--
--   and
--
--   $$g(x)\ge g(\bar x)+\langle-A^\top\bar y,x-\bar x\rangle+\frac\alpha2\operatorname{dist}^2\bigl(x,(\partial g)^{-1}(-A^\top\bar y)\bigr)\quad(x\in\mathcal X).$$
--
--   These estimates quantify the component growth used in the proof of Theorem 4.2.
--
--   **Formalization Note.** The source prints $c,\alpha\ge0$, while Definition 4.1 and the subsequent positive-growth conclusion require them to be strictly positive; the inequality signs here record that intended reading.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 11, (4.5) and following display

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

namespace ErrBoundQG.Structured

open scoped InnerProductSpace

/-- Component quadratic growth (4.5) and the following display, §4, p. 11. -/
theorem eq_4_5 {m n : ℕ}
    (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (hSbd : Bornology.IsBounded S) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hnd : DualNondegenerate f g A)
    (hsc : DualStrictComplementarity f g A ybar)
    (hffirm : FirmlyConvexRel (fun z => (f z : EReal)) ybar)
    (hgfirm : FirmlyConvexRel g (-(ContinuousLinearMap.adjoint A ybar)))
    (φstar : ℝ) (hstar : ∀ x ∈ S, primalObj f g A x = (φstar : EReal))
    (ν : ℝ) (hν : 0 < ν) (xbar : E n) (hxbar : xbar ∈ S) :
    let X : Set (E n) := {x | primalObj f g A x ≤ ((φstar + ν : ℝ) : EReal)}
    let Y : Set (E m) := A '' X
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (∀ y ∈ Y,
        f (A xbar) + ⟪ybar, y - A xbar⟫_ℝ +
          c / 2 * Metric.infDist y
            {z : E m | ybar ∈ ProxAlg.FixedPoint.subdifferential
              (fun w => (f w : EReal)) z} ^ 2 ≤ f y) ∧
      (∀ x ∈ X,
        g xbar + ((⟪-(ContinuousLinearMap.adjoint A ybar), x - xbar⟫_ℝ +
          α / 2 * Metric.infDist x
            {z : E n | -(ContinuousLinearMap.adjoint A ybar) ∈
              ProxAlg.FixedPoint.subdifferential g z} ^ 2 : ℝ) : EReal) ≤ g x) := by sorry

end ErrBoundQG.Structured
