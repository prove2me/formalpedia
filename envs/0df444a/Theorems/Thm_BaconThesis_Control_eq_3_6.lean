-- Prove2me | Theorems.Thm_BaconThesis_Control_eq_3_6
-- name    : BaconThesis.Control.eq_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:46.948574+00:00
-- url     : https://prove2.me/theorems/7f3214d7-225b-4554-8204-0165f967de87
-- title:
--   (3.6) — differentiating the control condition at $t = 0$ (corrected: $H$ in place of $H_{SA}$)
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on $\mathcal H_S\otimes\mathcal H_A$, $|a\rangle$ an apparatus vector and $H_a$ a Hermitian system operator such that the pure state stationary control condition (3.2),
--   $$
--   U(t)\,\big(\rho_S\otimes|a\rangle\langle a|\big)\,U(t)^\dagger = U_a(t)\,\rho_S\,U_a(t)^\dagger\otimes|a\rangle\langle a|,
--   $$
--   holds for every real $t$ and every system density matrix $\rho_S$. Then for every system density matrix $\rho_S$
--   $$
--   \big[H,\ \rho_S\otimes|a\rangle\langle a|\big] = [H_a,\ \rho_S]\otimes|a\rangle\langle a| .
--   $$
--
--   This is the first step of the necessity argument: it turns the dynamical condition (3.2) into an algebraic one.
--
--   Differences from the source:
--   - correction: [H_SA, ρ_S(0) ⊗ |a⟩⟨a|] with the coupling term H_SA of (3.1) → the commutator with the full Hamiltonian H; reason: the printed form is false: for qubits, H = σ_z ⊗ I (H_S = σ_z, H_A = 0, H_SA = 0), H_a = σ_z, any unit |a⟩ and ρ_S = |+⟩⟨+| satisfy (3.2), but [H_SA, ·] = 0 while [σ_z, |+⟩⟨+|] ⊗ |a⟩⟨a| ≠ 0; the derivative of (3.2) at t = 0 is the commutator with H, which is what (3.7)–(3.8) use
--   - generalization: |a⟩ a pure state of an orthogonal set → any apparatus vector; reason: the derivative at t = 0 uses nothing about |a⟩; the book's states are instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, eq. (3.6), p.32 (PDF p.49)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_evol

open scoped Kronecker Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, eq. (3.6), p.32 (PDF p.49): "Differentiating the orthogonal pure state stationary control
condition, Eq. (3.2), with respect to time t and evaluating this equation at t = 0 we find that
[HSA, ρS(0) ⊗ |a⟩⟨a|] = [Ha, ρS(0)] ⊗ |a⟩⟨a|." If a Hermitian `H` and a Hermitian `H_a` satisfy
(3.2) for the apparatus vector `|a⟩` (for all `t` and all density matrices `ρ_S`), then for every
density matrix `ρ_S`, `[H, ρ_S ⊗ |a⟩⟨a|] = [H_a, ρ_S] ⊗ |a⟩⟨a|`.

**Formalization Note.** The commutator on the left is with the full Hamiltonian `H` of (3.1),
not with the coupling term `H_SA` printed on the page (corrected: the printed form fails for
`H = H_S ⊗ I`, `H_SA = 0`, `H_a = H_S`). `|a⟩` is any vector. -/
theorem eq_3_6 {s a : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian) (v : a → ℂ)
    (Ha : Matrix s s ℂ) (hHa : Ha.IsHermitian)
    (h32 : ∀ t : ℝ, ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      evol H t * (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * (evol H t)ᴴ =
        (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ Matrix.vecMulVec v (star v)) :
    ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      H * (ρ ⊗ₖ Matrix.vecMulVec v (star v)) - (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * H =
        (Ha * ρ - ρ * Ha) ⊗ₖ Matrix.vecMulVec v (star v) := by sorry

end BaconThesis.Control
