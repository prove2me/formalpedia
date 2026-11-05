-- Prove2me | Theorems.Thm_FermionModewise_kappa_zero_decouple
-- name    : FermionModewise.kappa_zero_decouple
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:14.503871+00:00
-- url     : https://prove2.me/theorems/a0d1551e-222c-4666-aca3-67ec7b197ef5
-- title:
--   Local modes with eigenvalue $\lambda_0$ decouple
-- statement:
--   Let $\lambda_0\ge0$, let $g_A$, $g_B$ be arbitrary numbers of modes, and let
--   $$\widetilde M_{\lambda_0}=\begin{pmatrix}\lambda_0J_{2g_A}&\tilde K_{\lambda_0}\\-\tilde K_{\lambda_0}^T&\lambda_0J_{2g_B}\end{pmatrix}$$
--   satisfy $\widetilde M_{\lambda_0}^2=-\lambda_0^2\,\mathbb 1$. Then $\tilde K_{\lambda_0}=0$.
--
--   So local modes whose Williamson eigenvalue equals $\lambda_0$ are not correlated with the other side; in the pure case $\lambda_0=1$ they end up in the vacuum.
--
--   Differences from the source:
--   - encoding: degeneracies g_A, g_B and λ0J_{2g} = ⊕λ0J₂ → finite mode types α, β and the Williamson form with all eigenvalues λ0; reason: relabelling only, the same matrices
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, p.8 (after (22))

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace FermionModewise

/-- **Modes with eigenvalue `λ₀` decouple** (Botero–Reznik, arXiv:quant-ph/0404176v3, p.8): for
`λ = λ₀`, if `M̃_{λ₀} = [[λ₀ J_{2g_A}, K̃_{λ₀}], [−K̃_{λ₀}ᵀ, λ₀ J_{2g_B}]]` satisfies `M̃_{λ₀}² = −λ₀²`,
then `K̃_{λ₀} = 0`, whatever the degeneracies `g_A`, `g_B`.

**Formalization Note.** The mode types `α`, `β` are unrelated (the degeneracies are not
restricted). -/
theorem kappa_zero_decouple {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam0 : ℝ) (hlam0 : 0 ≤ lam0) (K : Matrix (α × Fin 2) (β × Fin 2) ℝ)
    (h : Matrix.fromBlocks (williamson fun _ : α => lam0) K (-Kᵀ) (williamson fun _ : β => lam0) *
        Matrix.fromBlocks (williamson fun _ : α => lam0) K (-Kᵀ) (williamson fun _ : β => lam0) =
      (-(lam0 ^ 2)) • (1 : Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)) :
    K = 0 := by sorry

end FermionModewise
