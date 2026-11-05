-- Prove2me | Theorems.Thm_FermionModewise_eq_20b
-- name    : FermionModewise.eq_20b
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:03.775065+00:00
-- url     : https://prove2.me/theorems/33c33dd1-9154-45dd-a252-4b74e6850e84
-- title:
--   Equation (20b): $J_{2g_A}\tilde K_\lambda J_{2g_B}=\tilde K_\lambda$ (corrected: requires $\lambda\ne0$)
-- statement:
--   Let $\lambda,\lambda_0\ge0$ with $\lambda\ne0$, and let $\widetilde M_\lambda=\begin{pmatrix}\lambda J_{2g_A}&\tilde K_\lambda\\-\tilde K_\lambda^T&\lambda J_{2g_B}\end{pmatrix}$ satisfy $\widetilde M_\lambda^2=-\lambda_0^2\,\mathbb 1$. Then
--   $$J_{2g_A}\,\tilde K_\lambda\,J_{2g_B}=\tilde K_\lambda. \tag{20b}$$
--
--   Together with (20a), this makes the matrix $Q_\lambda$ of (21) orthogonal and symplectic.
--
--   Differences from the source:
--   - correction: (20b) for every λ → only for λ ≠ 0; reason: the printed statement is false at λ = 0: take g_A = g_B = 1, λ = 0, λ0 = 1, K̃_λ = 1₂, so M̃_λ = [[0, 1₂], [−1₂, 0]] and M̃_λ² = −1₄, yet J₂ 1₂ J₂ = −1₂ ≠ 1₂ (the page divides (18) by λ)
--   - encoding: J_{2g} = ⊕J₂ → the Williamson form with all eigenvalues 1; reason: the same matrix
--   - encoding: degeneracies g_A, g_B → finite mode types α, β; reason: relabelling only
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (20b), p.7

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace FermionModewise

/-- **Equation (20b), corrected** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (20b), p.7): for
`M̃_λ = [[λ J_{2g_A}, K̃_λ], [−K̃_λᵀ, λ J_{2g_B}]]` with `M̃_λ² = −λ₀²` and **`λ ≠ 0`**,
`J_{2g_A} K̃_λ J_{2g_B} = K̃_λ`.

**Formalization Note.** The printed (20b) has no condition on `λ` and is false at `λ = 0`
(`λ₀ = 1`, `g_A = g_B = 1`, `K̃ = 1₂`: then `M̃² = −1` but `J₂ 1₂ J₂ = −1₂`); the hypothesis
`λ ≠ 0` is the minimal correction. `J_{2g}` is `williamson (fun _ => 1)`. -/
theorem eq_20b {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam lam0 : ℝ) (hlam : 0 ≤ lam) (hlam0 : 0 ≤ lam0) (hlam_ne : lam ≠ 0)
    (K : Matrix (α × Fin 2) (β × Fin 2) ℝ)
    (h : Matrix.fromBlocks (williamson fun _ : α => lam) K (-Kᵀ) (williamson fun _ : β => lam) *
        Matrix.fromBlocks (williamson fun _ : α => lam) K (-Kᵀ) (williamson fun _ : β => lam) =
      (-(lam0 ^ 2)) • (1 : Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)) :
    williamson (fun _ : α => (1 : ℝ)) * K * williamson (fun _ : β => (1 : ℝ)) = K := by sorry

end FermionModewise
