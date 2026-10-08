-- Prove2me | Theorems.Thm_ExpConeIPM_Secant_L_mul_Vt
-- name    : ExpConeIPM.Secant.L_mul_Vt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:41.612983+00:00
-- url     : https://prove2.me/theorems/b1bebc33-9302-4736-bfcf-9792f16ed70d
-- title:
--   Proof of Theorem 2: LVᵀ = Y₀ᵀ
-- statement:
--   Let $Y_0, S_0 \in \mathbb{R}^{n\times p}$ with $Y_0^TS_0$ symmetric positive definite, let $V = (v_1 \cdots v_p)$ be produced by the recursion (25)–(26), and let $L$ be the $p\times p$ matrix whose $k$-th column is $Y_{k-1}^TS_{k-1}e_k/\langle Y_{k-1}e_k, S_{k-1}e_k\rangle^{1/2}$. Then
--
--   $$
--   LV^{T} = Y_0^{T} .
--   $$
--
--   Combined with $LL^T = Y_0^TS_0$ this gives $Y_0(Y_0^TS_0)^{-1}Y_0^T = Y_0(LL^T)^{-1}Y_0^T = VV^T$, the first identity of Theorem 2.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 359, §5, proof of Theorem 2

import Mathlib
import Definitions.Def_ExpConeIPM_Secant_Recursion

namespace ExpConeIPM.Secant

open Matrix

/-- Dahl–Andersen, Math. Program. 194 (2022), §5, proof of Theorem 2, p. 359.
If Y₀ᵀS₀ is symmetric positive definite then LVᵀ = Y₀ᵀ. -/
theorem L_mul_Vt {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (hPD : (Y₀ᵀ * S₀).PosDef) :
    L Y₀ S₀ * (V Y₀ S₀)ᵀ = Y₀ᵀ := by sorry

end ExpConeIPM.Secant
