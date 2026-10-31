-- Prove2me | Theorems.Thm_BSPConvex_CMM_theorem_2
-- name    : BSPConvex.CMM.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:51.888594+00:00
-- url     : https://prove2.me/theorems/1c0c5f73-8f05-4c09-a4da-79cba4c1c30f
-- title:
--   Theorem 2, p. 9 — for Σ ≻ 0 the BSP-CMM profit π(q) of (6) is concave on the open simplex
-- statement:
--   Let $\omega,c\in\mathbb R^m$ and let $\Sigma\in\mathbb R^{m\times m}$ be positive definite, $\Sigma\succ0$. For $q\in\operatorname{int}(\Delta_m)=\{q\in\mathbb R^m: e^\top q<1,\ q>0\}$ put $S(q)=\operatorname{Diag}(q)-qq^\top$, $T(q)=\Sigma^{1/2}S(q)\Sigma^{1/2}$ and
--   $$\pi(q)=q^\top(\omega-c)+\tfrac12 q^\top\operatorname{diag}\big(\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}\big)-q^\top\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}q .$$
--   Then $\pi$ is concave on $\operatorname{int}(\Delta_m)$.
--
--   In the bundle size pricing problem under the cross moment model, $\omega$ and $\Sigma$ are the mean and covariance of the customers' bundle valuations, $c$ the bundle costs, and $\pi(q)$ the expected profit when prices are set so that the choice probabilities are $q$ (Problem (6)). The theorem makes the pricing problem a concave maximization, hence tractable.
--
--   **Formalization Note** The paper writes Problem (6) over $\Delta_m$. The function $\pi$ involves $(T(q))^{-1/2}$, and $T(q)$ is singular on the boundary of $\Delta_m$, so the statement is made on $\operatorname{int}(\Delta_m)$, the set of choice probabilities that the model generates (Lemma 2); the formal inverse would be $0$ on the boundary. $\Sigma\succ0$ is `Sig.PosDef` (which includes symmetry); $A^{1/2}$ is `CFC.sqrt`. The interpretation of $\pi$ as the expected profit rests on Theorem 1 and Lemmas 1–2 of the paper, which are not formalized here.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 9, Theorem 2 and Equation (6)

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem theorem_2 {m : ℕ} (ω c : Fin m → ℝ) (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef) :
    ConcaveOn ℝ (intSimplex m) (profit ω c Sig) := by sorry

end BSPConvex.CMM
