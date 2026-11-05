-- Prove2me | Theorems.Thm_FermionModewise_eq_17
-- name    : FermionModewise.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:26.049619+00:00
-- url     : https://prove2.me/theorems/e48e6942-7c03-4deb-ab9d-b4a8d0981c19
-- title:
--   Equation (17): $W_A\tilde K+\tilde KW_B=0$
-- statement:
--   Let $W_A$, $W_B$ be real square matrices, $\tilde K$ a real rectangular matrix, and $\lambda_0$ a real number. If the block matrix of (16)
--   $$\widetilde M=\begin{pmatrix}W_A&\tilde K\\-\tilde K^T&W_B\end{pmatrix}$$
--   satisfies $\widetilde M^2=-\lambda_0^2\,\mathbb 1$, then
--   $$W_A\tilde K+\tilde KW_B=0. \tag{17}$$
--
--   In the proof, $W_A$ and $W_B$ are the Williamson forms of the local covariance matrices, and (17) is the equation from which the decoupling of modes with different eigenvalues follows.
--
--   Differences from the source:
--   - generalization: W_A, W_B the local Williamson forms → arbitrary real square blocks; reason: (17) is the off-diagonal block of M̃² = −λ0², and Williamson blocks are an instance
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (16)–(17), p.6

import Mathlib

open Matrix

namespace FermionModewise

/-- **Equation (17)** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (17), p.6): if the total FCM
written in the block form (16), `M̃ = [[W_A, K̃], [−K̃ᵀ, W_B]]`, satisfies `M̃² = −λ₀²`, then
`W_A K̃ + K̃ W_B = 0`.

**Formalization Note.** The blocks `W_A`, `W_B` are arbitrary real square matrices (on the page they
are Williamson forms); the identity is the off-diagonal block of `M̃²`. -/
theorem eq_17 {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (WA : Matrix m m ℝ) (WB : Matrix n n ℝ) (K : Matrix m n ℝ) (lam0 : ℝ)
    (h : Matrix.fromBlocks WA K (-Kᵀ) WB * Matrix.fromBlocks WA K (-Kᵀ) WB =
      (-(lam0 ^ 2)) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℝ)) :
    WA * K + K * WB = 0 := by sorry

end FermionModewise
