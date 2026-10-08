-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_corollary_3_6
-- name    : ErrBoundQG.ProxGrad.corollary_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:15.246011+00:00
-- url     : https://prove2.me/theorems/f86bfc0c-f256-426c-bcf1-3ca0c00f6dba
-- title:
--   Corollary 3.6, p. 9 — for the proximal gradient method, quadratic growth and the error bound condition are equivalent, with explicit constants
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}$ be a proper closed convex function and $f:\mathbb R^n\to\mathbb R$ a convex $C^1$-smooth function whose gradient is $\beta$-Lipschitz, $\|\nabla f(x)-\nabla f(y)\|\le\beta\|x-y\|$. Suppose $\varphi := f+g$ has a nonempty set $S$ of minimizers, with minimal value $\varphi^*$. Fix $t>0$ and $\nu>0$, and let $\mathcal G_t(x) = t^{-1}\big(x - \operatorname{prox}_{tg}(x - t\nabla f(x))\big)$ be the prox-gradient mapping. Consider
--
--   1. **(Quadratic growth)** $\displaystyle \varphi(x)\ge\varphi^*+\frac{\alpha}{2}\operatorname{dist}^2(x;S)$ for all $x\in[\varphi\le\varphi^*+\nu]$; (3.12)
--   2. **(Error bound condition)** $\displaystyle \operatorname{dist}(x;S)\le\gamma\|\mathcal G_t(x)\|$ for all $x\in[\varphi\le\varphi^*+\nu]$. (3.13)
--
--   Then (3.12) with $\alpha>0$ implies (3.13) with
--   $$\gamma = (2\alpha^{-1}+t)(1+\beta t),$$
--   and conversely (3.13) with $\gamma>0$ implies (3.12) for every $\alpha\in(0,\gamma^{-1})$.
--
--   The error bound condition is what drives linear convergence of the proximal gradient method (Theorem 3.2), but it is phrased through the algorithm's own map $\mathcal G_t$; the corollary replaces it by the geometric condition that $\varphi$ grows quadratically away from its minimizers.
--
--   **Formalization Note** "Closed convex" is proper convex (`ProperConvex`: never $-\infty$, somewhere finite) plus lower semicontinuity; $\varphi = f + g$ is computed in `EReal`. $\varphi^*$ is a real number equal to $\varphi$ on $S$. The proximal step is the predicate `IsProxPoint (fun y => t * g y) (x - t∇f(x)) p`, and (3.13) is required for every such $p$ (it exists and is unique). The page writes both $\varphi^\star$ and $\varphi^*$ for the minimal value. No restriction $t\le\beta^{-1}$ is imposed: the corollary holds for every $t>0$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 9, Corollary 3.6, (3.12), (3.13)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxGrad_Setting

namespace ErrBoundQG.ProxGrad

theorem corollary_3_6 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : RockafellarMaxMono.Shared.ProperConvex g) (hgc : LowerSemicontinuous g)
    (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (β : ℝ) (hβ : 0 ≤ β) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S = minSet (compositeObj f g))
    (hSne : S.Nonempty) (φstar : ℝ) (hstar : ∀ x ∈ S, compositeObj f g x = (φstar : EReal))
    (t : ℝ) (ht : 0 < t) (ν : ℝ) (hν : 0 < ν) :
    (∀ α : ℝ, 0 < α → QuadGrowth (compositeObj f g) S φstar α ν →
        ErrorBound f g t S φstar ((2 * α⁻¹ + t) * (1 + β * t)) ν) ∧
    (∀ γ : ℝ, 0 < γ → ErrorBound f g t S φstar γ ν →
        ∀ α ∈ Set.Ioo 0 γ⁻¹, QuadGrowth (compositeObj f g) S φstar α ν) := by sorry

end ErrBoundQG.ProxGrad
