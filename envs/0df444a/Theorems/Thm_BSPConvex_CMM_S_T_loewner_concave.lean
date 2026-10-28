-- Prove2me | Theorems.Thm_BSPConvex_CMM_S_T_loewner_concave
-- name    : BSPConvex.CMM.S_T_loewner_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:41.906607+00:00
-- url     : https://prove2.me/theorems/4d31c3de-464f-49ea-9454-d0d0b8f4c686
-- title:
--   Proof of Lemma 6, p. 27 — S(λx + (1 − λ)y) = λS(x) + (1 − λ)S(y) + λ(1 − λ)(x − y)(x − y)ᵀ ⪰ λS(x) + (1 − λ)S(y), and likewise T
-- statement:
--   Let $\Sigma\succeq 0$, let $x,y\in\mathbb R^m$ and $\lambda\in[0,1]$. Then
--
--   1. $S(\lambda x+(1-\lambda)y)=\lambda S(x)+(1-\lambda)S(y)+\lambda(1-\lambda)(x-y)(x-y)^\top$;
--   2. $S(\lambda x+(1-\lambda)y)\succeq\lambda S(x)+(1-\lambda)S(y)$;
--   3. $T(\lambda x+(1-\lambda)y)\succeq\lambda T(x)+(1-\lambda)T(y)$,
--
--   where $S(x)=\operatorname{Diag}(x)-xx^\top$, $T(x)=\Sigma^{1/2}S(x)\Sigma^{1/2}$, and $A\succeq B$ means that $A-B$ is positive semidefinite.
--
--   These are the opening steps of the proof of Lemma 6: the matrix maps $S$ and $T$ are concave with respect to the Loewner order.
--
--   **Formalization Note** The paper states these steps inside the proof of Lemma 6, where $x,y\in\Delta_m$ and $\Sigma$ is a covariance matrix; the formal statement holds for all $x,y\in\mathbb R^m$ and every positive semidefinite $\Sigma$, which is a strengthening. $A\succeq B$ is written `(A - B).PosSemidef`.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 27, proof of Lemma 6

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem S_T_loewner_concave {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef)
    (x y : Fin m → ℝ) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    Smat (lam • x + (1 - lam) • y) =
        lam • Smat x + (1 - lam) • Smat y + (lam * (1 - lam)) • Matrix.vecMulVec (x - y) (x - y) ∧
      (Smat (lam • x + (1 - lam) • y) - (lam • Smat x + (1 - lam) • Smat y)).PosSemidef ∧
      (Tmat Sig (lam • x + (1 - lam) • y) - (lam • Tmat Sig x + (1 - lam) • Tmat Sig y)).PosSemidef := by sorry

end BSPConvex.CMM
