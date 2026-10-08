-- Prove2me | Theorems.Thm_ErrBoundQG_Structured_theorem_4_2
-- name    : ErrBoundQG.Structured.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:28.98136+00:00
-- url     : https://prove2.me/theorems/e0934d15-00e3-41c8-b8c9-9e6848032592
-- title:
--   Theorem 4.2, p. 11 — firm convexity and dual regularity give the proximal-gradient error bound
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be continuously differentiable and convex, let $g:\mathbb R^n\to(-\infty,+\infty]$ be proper, closed, and convex, and let $A:\mathbb R^n\to\mathbb R^m$ be linear. Suppose $\varphi(x)=f(Ax)+g(x)$ has a nonempty bounded solution set $S$, $\bar y$ solves its Fenchel dual, dual nondegeneracy and strict complementarity hold, and $f$ and $g$ are firmly convex relative to $\bar y$ and $-A^\top\bar y$. If $\nabla f$ is $\beta$-Lipschitz for some $\beta\ge0$, then for every step size $t>0$ there are $\gamma,\nu>0$ such that
--
--   $$\operatorname{dist}(x,S)\le\gamma\|G_t(x)\|\qquad\text{for all }x\text{ with }\varphi(x)\le\varphi^*+\nu,$$
--
--   where $G_t(x)=t^{-1}\bigl(x-\operatorname{prox}_{tg}(x-t\nabla(f\circ A)(x))\bigr)$.
--
--   This relates dual geometric conditions and growth of the components to a computable proximity measure for primal solutions.
--
--   **Formalization Note.** The Lipschitz-gradient hypothesis is made explicit because the paper reaches the error bound through Corollary 3.6, whose §3 setting requires it. The proximal point is represented by its argmin predicate; the inequality is asserted for every such point.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 11, Theorem 4.2; §3, pp. 4–5, Definition 3.1; p. 9, Corollary 3.6

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

namespace ErrBoundQG.Structured

/-- Theorem 4.2, §4, p. 11. -/
theorem theorem_4_2 {m n : ℕ}
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
    (β : ℝ) (hβ : 0 ≤ β)
    (hLip : ∀ y z : E m, ‖gradient f y - gradient f z‖ ≤ β * ‖y - z‖) :
    ∀ t : ℝ, 0 < t → ∃ γ ν : ℝ, 0 < γ ∧ 0 < ν ∧
      ErrorBound f g A t S φstar γ ν := by sorry

end ErrBoundQG.Structured
