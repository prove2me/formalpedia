-- Prove2me | Theorems.Thm_BSPConvex_CMM_g_identity
-- name    : BSPConvex.CMM.g_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:51.2062+00:00
-- url     : https://prove2.me/theorems/77725dab-f6d7-4a91-94ce-77274b26f8db
-- title:
--   Proof of Theorem 2, p. 28 — g(q) = −qᵀ∇f(q) = −½ tr(T(q)^{1/2}) + ½ qᵀΣ^{1/2}(T(q))^{−1/2}Σ^{1/2}q
-- statement:
--   Let $\Sigma\succ 0$ and $q\in\operatorname{int}(\Delta_m)$. Write $M(q)=\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}$ and $\nabla f(q)=\tfrac12\operatorname{diag}(M(q))-M(q)q$. Then $g(q)=-q^\top\nabla f(q)$ satisfies
--
--   1. $g(q)=-\tfrac12 q^\top\operatorname{diag}(M(q))+q^\top M(q)q$, and
--   2. $$g(q)=-\tfrac12\operatorname{tr}\big(T(q)^{1/2}\big)+\tfrac12 q^\top\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}q.$$
--
--   This is the chain of equalities that opens the proof of Theorem 2; it rewrites $g$ in a form whose epigraph can be described by matrix inequalities.
--
--   **Formalization Note** The last equality of the chain uses $T(q)\,T(q)^{-1/2}=T(q)^{1/2}$, which needs $T(q)$ invertible. That holds for $\Sigma\succ0$ exactly on $\operatorname{int}(\Delta_m)$, which is why the statement is made there (on the boundary the formal inverse is $0$). $(T(q))^{-1/2}$ is `(CFC.sqrt (T q))⁻¹`.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 28, proof of Theorem 2

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem g_identity {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    gFun Sig q = -(1 / 2 : ℝ) * (q ⬝ᵥ Matrix.diag (Mmat Sig q)) + q ⬝ᵥ (Mmat Sig q *ᵥ q) ∧
      gFun Sig q = -(1 / 2 : ℝ) * Matrix.trace (CFC.sqrt (Tmat Sig q)) +
        (1 / 2 : ℝ) * (q ⬝ᵥ (Mmat Sig q *ᵥ q)) := by sorry

end BSPConvex.CMM
