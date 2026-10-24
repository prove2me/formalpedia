-- Prove2me | Theorems.Thm_CtxInvOpt_Pointed_prop1_uncAngle_ellCone
-- name    : CtxInvOpt.Pointed.prop1_uncAngle_ellCone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:46.578196+00:00
-- url     : https://prove2.me/theorems/bdc853f9-b2bd-47ed-9a6f-6457e85c7314
-- title:
--   Proposition 1, p. 19 — the uncertainty angle of E(W, U) is arctan √λ_max(W)
-- statement:
--   Let $d=m+1\ge 2$, let $W=\operatorname{diag}(w_1,\dots,w_m)$ be positive definite and let $U\in\mathbb R^{d\times d}$ be orthonormal. Then the uncertainty angle of the ellipsoidal cone $E(W,U)$ is
--   $$\alpha\big(E(W,U)\big)=\arctan\sqrt{\lambda_{\max}(W)}.$$
--
--   The proposition translates the size of the cone's shape matrix into the quantity that, by Theorem 1, controls the one-period regret of the circumcenter policy. It is why the analysis of EllipsoidalCones must control the largest eigenvalue of $W_t$, not only their product.
--
--   **Formalization Note** $\lambda_{\max}(W)$ is the largest diagonal entry of $W$. The uncertainty angle is the paper's (9), with the convention $\theta(0,\hat c)=0$ for the apex $0\in E(W,U)$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 19, Proposition 1; proof App-11–App-12

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_EllCone

namespace CtxInvOpt.Pointed

open Matrix

/-- **Proposition 1, p. 19.** For `W = diag(w) ∈ D^{d−1}_{++}` (`d = m + 1 ≥ 2`) and an orthonormal `U`,
the uncertainty angle of the ellipsoidal cone is `α(E(W, U)) = arctan √λ_max(W)`. -/
theorem prop1_uncAngle_ellCone {m : ℕ} (hm : 1 ≤ m) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) :
    CtxInvOpt.Offline.uncAngle (ellCone w U) = Real.arctan (Real.sqrt (lamMax w)) := by sorry

end CtxInvOpt.Pointed
