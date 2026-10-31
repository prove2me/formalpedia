-- Prove2me | Theorems.Thm_BSPConvex_CMM_lemma_6
-- name    : BSPConvex.CMM.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:42.970611+00:00
-- url     : https://prove2.me/theorems/cf671971-017e-4ffa-90f9-0b4434f01e10
-- title:
--   Lemma 6, p. 27 — T(λx + (1 − λ)y)^{1/2} ⪰ λT(x)^{1/2} + (1 − λ)T(y)^{1/2} on Δm
-- statement:
--   Let $\Sigma\succeq 0$ and $T(x)=\Sigma^{1/2}S(x)\Sigma^{1/2}$ with $S(x)=\operatorname{Diag}(x)-xx^\top$. For all $x,y\in\Delta_m$ and $\lambda\in[0,1]$,
--   $$\big(T(\lambda x+(1-\lambda)y)\big)^{1/2}\succeq\lambda\,(T(x))^{1/2}+(1-\lambda)\,(T(y))^{1/2},$$
--   where $A^{1/2}$ is the positive semidefinite square root and $A\succeq B$ means $A-B$ is positive semidefinite.
--
--   The lemma says that $x\mapsto T(x)^{1/2}$ is concave on the simplex in the Loewner order. It is the main ingredient of the proof of Theorem 2: it gives concavity of $\operatorname{tr}(T(q)^{1/2})$ and convexity of the set $\{(q,Z): T(q)^{1/2}\succeq Z,\ q\in\Delta_m\}$.
--
--   **Formalization Note** The paper's $\Sigma$ is a covariance matrix; the formal statement assumes only that it is positive semidefinite (Mathlib's `PosSemidef`, which includes symmetry). The square root is `CFC.sqrt` on real matrices with the Loewner order of `MatrixOrder`.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 27, Lemma 6 (proof pp. 27–28)

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem lemma_6 {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef)
    (x y : Fin m → ℝ) (hx : x ∈ simplex m) (hy : y ∈ simplex m)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (CFC.sqrt (Tmat Sig (lam • x + (1 - lam) • y)) -
      (lam • CFC.sqrt (Tmat Sig x) + (1 - lam) • CFC.sqrt (Tmat Sig y))).PosSemidef := by sorry

end BSPConvex.CMM
