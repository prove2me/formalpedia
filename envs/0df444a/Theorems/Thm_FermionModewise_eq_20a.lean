-- Prove2me | Theorems.Thm_FermionModewise_eq_20a
-- name    : FermionModewise.eq_20a
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:15.471117+00:00
-- url     : https://prove2.me/theorems/f6ef568c-b2b0-4153-a034-cdd7415239fd
-- title:
--   Equation (20a): $\tilde K_\lambda\tilde K_\lambda^T=\kappa_\lambda^2\mathbb 1$, $\tilde K_\lambda^T\tilde K_\lambda=\kappa_\lambda^2\mathbb 1$, and $g_A=g_B$ for $\lambda\ne\lambda_0$
-- statement:
--   Let $\lambda,\lambda_0\ge0$, let $g_A$, $g_B$ be numbers of modes, and let
--   $$\widetilde M_\lambda=\begin{pmatrix}\lambda J_{2g_A}&\tilde K_\lambda\\-\tilde K_\lambda^T&\lambda J_{2g_B}\end{pmatrix},\qquad J_{2g}=\bigoplus_{i=1}^gJ_2, \tag{19}$$
--   satisfy $\widetilde M_\lambda^2=-\lambda_0^2\,\mathbb 1$. Then, with $\kappa_\lambda^2=\lambda_0^2-\lambda^2$,
--   $$\tilde K_\lambda\tilde K_\lambda^T=\kappa_\lambda^2\,\mathbb 1_{2g_A},\qquad \tilde K_\lambda^T\tilde K_\lambda=\kappa_\lambda^2\,\mathbb 1_{2g_B}, \tag{20a}$$
--   and if $\lambda\ne\lambda_0$ then $g_A=g_B$: the degeneracies of $\lambda$ in the two local spectra agree.
--
--   This is what pairs the $A$-modes and $B$-modes with a common local Williamson eigenvalue $\lambda<\lambda_0$.
--
--   Differences from the source:
--   - encoding: κ_λ² with κ_λ = √(λ0² − λ²) → λ0² − λ²; reason: the same number, written without a square root
--   - encoding: degeneracies g_A, g_B → finite mode types α, β, and g_A = g_B → card α = card β; reason: relabelling only
--   - encoding: λJ_{2g} = ⊕λJ₂ → the Williamson form with all eigenvalues λ; reason: the same matrix
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (19)–(20a) and the trace argument after (20b), p.7

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace FermionModewise

/-- **Equation (20a) and equal degeneracies** (Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (19)–
(20a), p.7): let `M̃_λ = [[λ J_{2g_A}, K̃_λ], [−K̃_λᵀ, λ J_{2g_B}]]` with `λ ≥ 0` and `λ₀ ≥ 0`
satisfy `M̃_λ² = −λ₀²`. Then `K̃_λ K̃_λᵀ = κ_λ² 1_{2g_A}` and `K̃_λᵀ K̃_λ = κ_λ² 1_{2g_B}` with
`κ_λ² = λ₀² − λ²`, and if `λ ≠ λ₀` the degeneracies agree, `g_A = g_B`.

**Formalization Note.** The `g_A` (resp. `g_B`) modes are indexed by a finite type `α` (resp. `β`),
and `λ J_{2g}` is `williamson (fun _ => λ)`. `κ_λ²` is written `λ₀² − λ²`. -/
theorem eq_20a {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam lam0 : ℝ) (hlam : 0 ≤ lam) (hlam0 : 0 ≤ lam0) (K : Matrix (α × Fin 2) (β × Fin 2) ℝ)
    (h : Matrix.fromBlocks (williamson fun _ : α => lam) K (-Kᵀ) (williamson fun _ : β => lam) *
        Matrix.fromBlocks (williamson fun _ : α => lam) K (-Kᵀ) (williamson fun _ : β => lam) =
      (-(lam0 ^ 2)) • (1 : Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)) :
    K * Kᵀ = (lam0 ^ 2 - lam ^ 2) • (1 : Matrix (α × Fin 2) (α × Fin 2) ℝ) ∧
      Kᵀ * K = (lam0 ^ 2 - lam ^ 2) • (1 : Matrix (β × Fin 2) (β × Fin 2) ℝ) ∧
      (lam ≠ lam0 → Fintype.card α = Fintype.card β) := by sorry

end FermionModewise
