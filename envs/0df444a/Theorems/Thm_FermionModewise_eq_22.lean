-- Prove2me | Theorems.Thm_FermionModewise_eq_22
-- name    : FermionModewise.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:08.987067+00:00
-- url     : https://prove2.me/theorems/4e7d81ac-2dae-42fc-9ab8-7a68ac01d5fe
-- title:
--   Equations (21)–(22): $Q_\lambda$ is orthogonal, and symplectic (corrected: symplectic only for $\lambda\ne0$)
-- statement:
--   Let $\lambda,\lambda_0\ge0$ with $\lambda\ne\lambda_0$, let $g_A=g_B=g$, and let $\widetilde M_\lambda=\begin{pmatrix}\lambda J_{2g}&\tilde K_\lambda\\-\tilde K_\lambda^T&\lambda J_{2g}\end{pmatrix}$ satisfy $\widetilde M_\lambda^2=-\lambda_0^2\,\mathbb 1$. Put $\kappa_\lambda=\sqrt{\lambda_0^2-\lambda^2}$ and define $Q_\lambda$ by (21),
--   $$\tilde K_\lambda=\kappa_\lambda\,Q_\lambda\,\beta,\qquad \beta=\bigoplus_{i=1}^g\begin{pmatrix}0&1\\1&0\end{pmatrix},$$
--   that is, $Q_\lambda=\kappa_\lambda^{-1}\tilde K_\lambda\beta$. Then
--   $$Q_\lambda Q_\lambda^T=Q_\lambda^TQ_\lambda=\mathbb 1_{2g}, \tag{22}$$
--   and, if $\lambda\ne0$, $Q_\lambda J_{2g}Q_\lambda^{-1}=J_{2g}$: $Q_\lambda$ is an orthogonal symplectic transformation.
--
--   The one-sided transformation $O_A=Q_\lambda^T$ then brings $\tilde K_\lambda$ to $\kappa_\lambda\beta$ without changing the block $\lambda J_{2g}$.
--
--   Differences from the source:
--   - correction: Q_λJ_{2g}Q_λ⁻¹ = J_{2g} for every λ → only for λ ≠ 0; reason: the printed statement is false at λ = 0: take g = 1, λ = 0, λ0 = 1, K̃_λ = 1₂; then M̃_λ² = −1₄, Q_λ = β, and βJ₂ = −J₂β ≠ J₂β
--   - reading: β ≡ ⊕_{i=1}^N (0 1; 1 0) → ⊕_{i=1}^g; reason: β multiplies the 2g × 2g block K̃_λ, so N is a misprint for g
--   - encoding: K̃_λ ≡ κQ_λβ and Q_λJ_{2g}Q_λ⁻¹ = J_{2g} → Q_λ := κ_λ⁻¹K̃_λβ and Q_λJ_{2g} = J_{2g}Q_λ; reason: β² = 1, and for orthogonal Q_λ the two forms are equivalent
--   - encoding: degeneracy g and J_{2g} = ⊕J₂ → a finite mode type γ and the Williamson form with all eigenvalues 1; reason: relabelling only, the same matrix
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (21)–(22), p.7

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace FermionModewise

/-- **Equations (21)–(22), corrected** (Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (21)–(22),
p.7): let `g_A = g_B = g` (modes indexed by `γ`), let `M̃_λ = [[λ J_{2g}, K̃_λ], [−K̃_λᵀ, λ J_{2g}]]`
with `λ, λ₀ ≥ 0`, `λ ≠ λ₀` and `M̃_λ² = −λ₀²`, put `κ_λ = √(λ₀² − λ²)` and define `Q_λ` by
`K̃_λ = κ_λ Q_λ β` (21), i.e. `Q_λ = κ_λ⁻¹ K̃_λ β` with `β = ⊕ [[0, 1], [1, 0]]`. Then
`Q_λ Q_λᵀ = Q_λᵀ Q_λ = 1_{2g}`, and, **if `λ ≠ 0`**, `Q_λ J_{2g} Q_λ⁻¹ = J_{2g}`.

**Formalization Note.** Since `β² = 1`, (21) determines `Q_λ = κ_λ⁻¹ K̃_λ β`. The symplectic clause
is written `Q_λ J_{2g} = J_{2g} Q_λ`, equivalent to the printed form for orthogonal `Q_λ`. The
printed (22) has no condition on `λ` and its symplectic clause is false at `λ = 0` (`λ₀ = 1`,
`g = 1`, `K̃ = 1₂`: then `Q = β` and `β J₂ = −J₂ β`); `λ ≠ 0` is the minimal correction, and the
orthogonality clause is kept unconditional. The page prints `⊕_{i=1}^N` in (21); it is read as
`⊕_{i=1}^g`. -/
theorem eq_22 {γ : Type} [Fintype γ] [DecidableEq γ]
    (lam lam0 : ℝ) (hlam : 0 ≤ lam) (hlam0 : 0 ≤ lam0) (hne : lam ≠ lam0)
    (K : Matrix (γ × Fin 2) (γ × Fin 2) ℝ)
    (h : Matrix.fromBlocks (williamson fun _ : γ => lam) K (-Kᵀ) (williamson fun _ : γ => lam) *
        Matrix.fromBlocks (williamson fun _ : γ => lam) K (-Kᵀ) (williamson fun _ : γ => lam) =
      (-(lam0 ^ 2)) • (1 : Matrix ((γ × Fin 2) ⊕ (γ × Fin 2)) ((γ × Fin 2) ⊕ (γ × Fin 2)) ℝ)) :
    let kap : ℝ := Real.sqrt (lam0 ^ 2 - lam ^ 2)
    let β : Matrix (γ × Fin 2) (γ × Fin 2) ℝ := Matrix.of fun p q =>
      if p.1 = q.1 then (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) p.2 q.2 else 0
    let Q : Matrix (γ × Fin 2) (γ × Fin 2) ℝ := kap⁻¹ • (K * β)
    Q * Qᵀ = 1 ∧ Qᵀ * Q = 1 ∧
      (lam ≠ 0 →
        Q * williamson (fun _ : γ => (1 : ℝ)) = williamson (fun _ : γ => (1 : ℝ)) * Q) := by sorry

end FermionModewise
