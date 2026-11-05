-- Prove2me | Theorems.Thm_FermionModewise_isotropic_normal_form
-- name    : FermionModewise.isotropic_normal_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:42.580452+00:00
-- url     : https://prove2.me/theorems/d4cde59b-38ea-43e8-aff2-563071bb1fc8
-- title:
--   Isotropic normal form (11)–(12) by local orthogonal transformations
-- statement:
--   Let $M$ be a real antisymmetric matrix on the quadratures of $m$ modes $A$ and $n$ modes $B$, and suppose
--   $$M^2=-\lambda_0^2\,\mathbb 1,\qquad\lambda_0\ge0. \tag{10}$$
--   Then there are real orthogonal matrices $O_A$ (on the $A$ quadratures) and $O_B$ (on the $B$ quadratures), a number $s$, injective pairings of $s$ $A$-modes with $s$ $B$-modes, and numbers $\lambda_k\ge0$, $\kappa_k>0$ with $\kappa_k^2+\lambda_k^2=\lambda_0^2$ ($k=1,\dots,s$), such that
--   $$(O_A\oplus O_B)\,M\,(O_A\oplus O_B)^T=\widetilde M_{\tilde A_1\tilde B_1}\oplus\cdots\oplus\widetilde M_{\tilde A_s\tilde B_s}\oplus\widetilde M_{\tilde A_F}\oplus\widetilde M_{\tilde B_F}, \tag{11}$$
--   where each $\widetilde M_{\tilde A_k\tilde B_k}$ is the block (12) with parameters $\lambda_k,\kappa_k$ on the $k$-th pair, and $\widetilde M_{\tilde A_F}$, $\widetilde M_{\tilde B_F}$ are $\lambda_0J_2$ on every remaining mode. In particular $s\le\min(m,n)$.
--
--   At $\lambda_0=1$ this is the covariance-matrix form of the main result.
--
--   Differences from the source:
--   - generalization: M the FCM of an isotropic Gaussian state, M² = −λ0² with λ0 ≤ 1 → every real antisymmetric M with M² = −λ0², λ0 ≥ 0; reason: the proof uses only these matrix properties, and every isotropic FCM is such a matrix
--   - generalization: (12) with κ_i² + λ_i² = λ0², and remaining blocks "isotropic FCM's with Williamson eigenvalue λ0" → additionally λ_k ≥ 0 and κ_k > 0, and the remaining blocks equal to λ0J₂ on each mode; reason: a stronger conclusion, the normalization the proof produces (local Williamson forms with λ ≥ 0, κ_λ = √(λ0² − λ²) for λ ≠ λ0); it implies the printed one
--   - encoding: "upon re-ordering the modes" → pairs given by injective maps p_A, p_B; reason: re-ordering is a permutation, which the local orthogonal transformations can absorb
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (10)–(12), pp.5–6; proof pp.6–8

import Mathlib
import Definitions.Def_FermionModewise_normalForm

open Matrix

namespace FermionModewise

/-- **Isotropic normal form** (Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (10)–(12), pp.5–6): let
`M` be a real antisymmetric matrix on the quadratures `(α × Fin 2) ⊕ (β × Fin 2)` of A-modes and
B-modes with `M² = −λ₀²`, `λ₀ ≥ 0`. Then there are local orthogonal transformations `O_A`, `O_B`,
a number `s` of pairs, injective pairings `pA : Fin s ↪ α`, `pB : Fin s ↪ β`, and parameters
`λ_k ≥ 0`, `κ_k > 0` with `κ_k² + λ_k² = λ₀²`, such that `(O_A ⊕ O_B) M (O_A ⊕ O_B)ᵀ` is the normal
form (11): the block (12) on each pair `(Ã_{pA k}, B̃_{pB k})`, `λ₀ J₂` on every other mode.

**Formalization Note.** "The FCM of an isotropic Gaussian state" is generalized to every real
antisymmetric `M` with `M² = −λ₀²`; the bound `λ₀ ≤ 1` of (10) is not needed and dropped. The
re-ordering of modes is encoded by the embeddings `pA`, `pB`, which give `s ≤ min(m, n)`. -/
theorem isotropic_normal_form {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (M : Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)
    (lam0 : ℝ) (hlam0 : 0 ≤ lam0) (hM : Mᵀ = -M)
    (hsq : M * M = (-(lam0 ^ 2)) • (1 : Matrix ((α × Fin 2) ⊕ (β × Fin 2))
      ((α × Fin 2) ⊕ (β × Fin 2)) ℝ)) :
    ∃ OA ∈ Matrix.orthogonalGroup (α × Fin 2) ℝ, ∃ OB ∈ Matrix.orthogonalGroup (β × Fin 2) ℝ,
      ∃ (s : ℕ) (pA : Fin s ↪ α) (pB : Fin s ↪ β) (lam kap : Fin s → ℝ),
        (∀ k, 0 ≤ lam k ∧ 0 < kap k ∧ kap k ^ 2 + lam k ^ 2 = lam0 ^ 2) ∧
        Matrix.fromBlocks OA 0 0 OB * M * (Matrix.fromBlocks OA 0 0 OB)ᵀ =
          normalForm pA pB lam kap lam0 := by sorry

end FermionModewise
