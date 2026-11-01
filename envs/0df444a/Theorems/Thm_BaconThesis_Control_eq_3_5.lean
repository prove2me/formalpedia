-- Prove2me | Theorems.Thm_BaconThesis_Control_eq_3_5
-- name    : BaconThesis.Control.eq_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:56.246376+00:00
-- url     : https://prove2.me/theorems/1c43c43d-da61-49a9-8007-3dbda351c445
-- title:
--   (3.5) — the eigenvalue conditions (3.4) give stationary control with $H_a = \lambda_a I_S + \sum_{\alpha\neq0} c_{\alpha,a}F_\alpha$
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on $\mathcal H_S\otimes\mathcal H_A$, $(F_\alpha)$ a fixed basis of the system operators with $F_0 = I/\sqrt d$, and $A_\alpha$, $H_A$ the operators of the expansion $H = I_S\otimes H_A + \sum_{\alpha\neq0}F_\alpha\otimes A_\alpha$. Let $|a\rangle$ be a unit apparatus vector with
--   $$
--   A_\alpha|a\rangle = c_{\alpha,a}|a\rangle\quad(\alpha\neq0),\qquad H_A|a\rangle = \lambda_a|a\rangle .
--   $$
--   Then $H_a = \lambda_a I_S + \sum_{\alpha\neq0}c_{\alpha,a}F_\alpha$ is Hermitian, and for every real $t$ and every system density matrix $\rho_S$
--   $$
--   U(t)\,\big(\rho_S\otimes|a\rangle\langle a|\big)\,U(t)^\dagger = U_a(t)\,\rho_S\,U_a(t)^\dagger\otimes|a\rangle\langle a|,
--   $$
--   with $U(t) = \exp[-iHt]$, $U_a(t) = \exp[-iH_a t]$.
--
--   This is the sufficiency half of the pure state stationary control criterion, with the controlled Hamiltonian written out.
--
--   **Formalization Note** The eigenvalues are taken in $\mathbb C$; the Hermiticity of $H_a$ is part of the conclusion and forces them to be real.
--
--   Differences from the source:
--   - encoding: A_α and H_A given by the expansion (3.3) → A_α = Tr_S[(F_α ⊗ I)H] and H_A = Tr_S[H]/d; reason: for a trace-orthonormal Hermitian basis these are the unique operators of (3.3); same instances
--   - encoding: eigenvalues c_{α,a}, λ_a (real) → complex numbers, Hermiticity of H_a in the conclusion; reason: for Hermitian A_α, H_A and a unit vector the eigenvalues are real; same instances
--   - generalization: |a⟩ a member of an orthogonal set 𝒜 of pure states → a single unit apparatus vector, with no orthogonality to other states; reason: the computation (3.5) is carried out for each |a⟩ separately and never uses the other states; the book's case is an instance
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, eqs. (3.4)–(3.5), p.32 (PDF p.49)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_evol
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA

open scoped Kronecker Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, eqs. (3.4)–(3.5), p.32 (PDF p.49): "Thus if Eq. (3.4) holds then the evolution is that of
orthogonal pure state stationary control with the controlled Hamiltonians
Ha = λaIS + Σ_{α≠0} cα,aFα." For a Hermitian `H`, a fixed basis `F` (index `i0` for `α = 0`) and a
unit apparatus vector `|a⟩` with `A_α|a⟩ = c_α|a⟩` (`α ≠ 0`) and `H_A|a⟩ = λ|a⟩`, the matrix
`H_a = λ I + Σ_{α≠0} c_α F_α` is Hermitian and for every `t` and every density matrix `ρ_S`,
`U(t)(ρ_S ⊗ |a⟩⟨a|)U(t)† = U_a(t) ρ_S U_a(t)† ⊗ |a⟩⟨a|`.

**Formalization Note.** `A_α = coeffOp H F α`, `H_A = HA H`, `U = evol`. The eigenvalues `c α`,
`λ` are taken complex; Hermiticity of `H_a` is part of the conclusion (it forces them real). The
value `c i0` is unused. -/
theorem eq_3_5 {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    [Fintype κ] [DecidableEq κ]
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (v : a → ℂ) (hv : star v ⬝ᵥ v = 1) (c : κ → ℂ) (lam : ℂ)
    (hc : ∀ α, α ≠ i0 → coeffOp H F α *ᵥ v = c α • v) (hl : HA H *ᵥ v = lam • v)
    (Ha : Matrix s s ℂ)
    (hHa : Ha = lam • (1 : Matrix s s ℂ) + ∑ α ∈ Finset.univ.erase i0, c α • F α) :
    Ha.IsHermitian ∧
      ∀ t : ℝ, ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
        evol H t * (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * (evol H t)ᴴ =
          (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ Matrix.vecMulVec v (star v) := by sorry

end BaconThesis.Control
