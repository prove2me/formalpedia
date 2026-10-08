-- Prove2me | Theorems.Thm_ExpConeIPM_Secant_theorem_2
-- name    : ExpConeIPM.Secant.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:31.213235+00:00
-- url     : https://prove2.me/theorems/1a305245-a94f-41cb-a085-06f7b476dbe9
-- title:
--   Theorem 2 — p rank-one steps give Y₀(Y₀ᵀS₀)⁻¹Y₀ᵀ = VVᵀ and S₀(Y₀ᵀS₀)⁻¹S₀ᵀ = UUᵀ
-- statement:
--   Let $Y_0, S_0 \in \mathbb{R}^{n\times p}$ with $Y_0^TS_0 \succ 0$ (symmetric positive definite). For $k = 1, \dots, p$, with $e_k$ the $k$-th unit vector of $\mathbb{R}^p$, define
--
--   $$
--   v_k := \frac{Y_{k-1}e_k}{\langle Y_{k-1}e_k, S_{k-1}e_k\rangle^{1/2}}, \qquad Y_k := Y_{k-1} - v_kv_k^{T}S_{k-1},
--   $$
--
--   $$
--   u_k := \frac{S_{k-1}e_k}{\langle Y_{k-1}e_k, S_{k-1}e_k\rangle^{1/2}}, \qquad S_k := S_{k-1} - u_ku_k^{T}Y_{k-1},
--   $$
--
--   and let $V := (v_1 \cdots v_p)$, $U := (u_1 \cdots u_p)$. Then
--
--   $$
--   Y_0(Y_0^{T}S_0)^{-1}Y_0^{T} = VV^{T}, \qquad S_0(Y_0^{T}S_0)^{-1}S_0^{T} = UU^{T}.
--   $$
--
--   The left-hand sides are the multiple-secant terms of the BFGS update $H_{\mathrm{BFGS}} = Y(Y^TS)^{-1}Y^T + H - HS(S^THS)^{-1}S^TH$ and of its inverse. The theorem computes them as sums of $p$ rank-one terms produced by a recursion resembling single-secant quasi-Newton updates; Dahl and Andersen use it to write the primal-dual scaling of their exponential-cone algorithm as a low-rank update.
--
--   **Formalization Note** "$Y_0^TS_0 \succ 0$" is read as symmetric positive definite (`Matrix.PosDef`, which includes symmetry). The symmetry is needed: with only $x^TY_0^TS_0x > 0$ for $x \ne 0$ the identities fail in general. The inverse is `Matrix.inv`, invertible under the hypothesis. $V$ and $U$ are computed by the recursion of the definition item, with 0-based column indices.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), pp. 357–358, Theorem 2

import Mathlib
import Definitions.Def_ExpConeIPM_Secant_Recursion

namespace ExpConeIPM.Secant

open Matrix

/-- Dahl–Andersen, Math. Program. 194 (2022), Theorem 2, pp. 357–358.
Given Y₀, S₀ ∈ ℝ^{n×p} with Y₀ᵀS₀ ≻ 0 (symmetric positive definite), the matrices
V = (v₁ ⋯ v_p) and U = (u₁ ⋯ u_p) produced by the recursions (25)–(26) satisfy
Y₀(Y₀ᵀS₀)⁻¹Y₀ᵀ = VVᵀ and S₀(Y₀ᵀS₀)⁻¹S₀ᵀ = UUᵀ. -/
theorem theorem_2 {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (hPD : (Y₀ᵀ * S₀).PosDef) :
    Y₀ * (Y₀ᵀ * S₀)⁻¹ * Y₀ᵀ = V Y₀ S₀ * (V Y₀ S₀)ᵀ ∧
      S₀ * (Y₀ᵀ * S₀)⁻¹ * S₀ᵀ = U Y₀ S₀ * (U Y₀ S₀)ᵀ := by sorry

end ExpConeIPM.Secant
