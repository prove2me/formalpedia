-- Prove2me | Theorems.Thm_BSPConvex_CMM_gradient_f
-- name    : BSPConvex.CMM.gradient_f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:58.774204+00:00
-- url     : https://prove2.me/theorems/d2375c41-f45a-426b-9396-da76b761033a
-- title:
--   §4.1, p. 9 — for Σ ≻ 0 the gradient of f at q ∈ int(Δm) is ½ diag(Σ^{1/2}T(q)^{−1/2}Σ^{1/2}) − Σ^{1/2}T(q)^{−1/2}Σ^{1/2}q
-- statement:
--   Let $\Sigma\succ0$ and $q\in\operatorname{int}(\Delta_m)$. The function $f(x)=\operatorname{tr}\big((\Sigma^{1/2}S(x)\Sigma^{1/2})^{1/2}\big)$ is differentiable at $q$ and its gradient is
--   $$\nabla f(q)=\tfrac12\operatorname{diag}\big(\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}\big)-\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}q,\qquad T(q)=\Sigma^{1/2}S(q)\Sigma^{1/2}.$$
--
--   The paper states this formula (attributing the surrounding analysis to Ahipaşaoğlu et al. 2018). Through the first-order condition $p-\omega=\nabla f(q)$ of Theorem 1 it gives the price as a function of the choice probabilities, which is how the profit (6) arises.
--
--   **Formalization Note** Differentiability is Fréchet differentiability of $f:\mathbb R^m\to\mathbb R$ at $q$ (`HasFDerivAt`), with derivative the linear functional $v\mapsto\nabla f(q)^\top v$ written as $\sum_i \nabla f(q)_i\,\mathrm{proj}_i$. The sentence of p. 9 also cites strong concavity of $f$; that claim is not part of this statement.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 9, §4.1 (gradient of f)

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem gradient_f {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    HasFDerivAt (fCMM Sig)
      (∑ i, gradF Sig q i • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) q := by sorry

end BSPConvex.CMM
