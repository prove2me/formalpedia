-- Prove2me | Theorems.Thm_BaconThesis_Control_mixed_stationary_control_iff
-- name    : BaconThesis.Control.mixed_stationary_control_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:31.681477+00:00
-- url     : https://prove2.me/theorems/2e24d8b6-6a9d-4d77-a829-4a893cd61f4c
-- title:
--   §3.2.2 — mixed state stationary control holds iff $A_\alpha\rho_a = c_{\alpha,a}\rho_a$ and $[H_A,\rho_a] = 0$ (corrected: $[H_A, \rho_a] = 0$ in place of $H_A \rho_a = \lambda_a \rho_a$)
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on $\mathcal H_S\otimes\mathcal H_A$, $(F_\alpha)$ a fixed basis of the system operators with $F_0 = I/\sqrt d$, and $A_\alpha$, $H_A$ the operators of the expansion
--   $$
--   H = I_S\otimes H_A + \sum_{\alpha\neq0}F_\alpha\otimes A_\alpha .
--   $$
--   Let $M$ be a set of density operators of the apparatus. Then $H$ performs mixed state stationary control for $M$ (condition (3.10)) if and only if for every $\rho_a\in M$
--   $$
--   A_\alpha\rho_a = c_{\alpha,a}\,\rho_a\quad(\alpha\neq0) \tag{3.11}
--   $$
--   for some numbers $c_{\alpha,a}$, and
--   $$
--   H_A\,\rho_a = \rho_a\,H_A .
--   $$
--
--   For a pure state $\rho_a = |a\rangle\langle a|$ the conditions are the pure state conditions (3.4), so this criterion contains the pure state one.
--
--   Differences from the source:
--   - correction: (3.12) H_A ρ_a = λ_a ρ_a → [H_A, ρ_a] = 0; reason: (3.12) is not necessary: for qubits, H = I ⊗ σ_z (so H_A = σ_z, A_α = 0 for α ≠ 0) and M = {I/2} satisfy (3.10) with H_a = 0, but σ_z · I/2 is no multiple of I/2; the two conditions agree for pure ρ_a
--   - generalization: a commuting set M of mixed states → any set of density operators; reason: the corrected criterion treats each ρ_a separately and does not use the commutation; the book's sets are instances
--   - encoding: eigenvalues c_{α,a} → complex numbers; reason: they are automatically real (c = Tr[A_α ρ_a]); same instances
--   - encoding: A_α and H_A given by the expansion (3.3) → A_α = Tr_S[(F_α ⊗ I)H] and H_A = Tr_S[H]/d; reason: for a trace-orthonormal Hermitian basis these are the unique operators of (3.3); same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.2, eqs. (3.10)–(3.12), p.33 (PDF p.50), proof (3.13)–(3.16), p.34 (PDF p.51)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA
import Definitions.Def_BaconThesis_Control_StationaryControlMixed

open scoped Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.2, eqs. (3.10)–(3.12), p.33 (PDF p.50), proof p.34 (PDF p.51), **corrected**: "We claim that a
necessary and sufficient condition for commuting mixed state stationary control is
Aαρa = cα,aρa (3.11) HAρa = λaρa, (3.12) for all of the commuting ρa." For a Hermitian `H`, a
fixed basis `F` (index `i0` for `α = 0`) and a set `M` of apparatus density operators, `H` performs
mixed state stationary control for `M` iff for every `ρ_a ∈ M`, `A_α ρ_a = c_{α,a} ρ_a` for every
`α ≠ 0` (3.11) and `[H_A, ρ_a] = 0`.

**Formalization Note.** The commutation `H_A ρ_a = ρ_a H_A` replaces the printed (3.12)
`H_A ρ_a = λ_a ρ_a`, which is not necessary: for qubits, `H = I ⊗ σ_z` and `M = {I/2}` satisfy (3.10)
with `H_a = 0`, but `σ_z (I/2)` is no multiple of `I/2`. For a pure `ρ_a = |a⟩⟨a|` the two coincide.
The book's `M` is a commuting set; the commutation is not used and not assumed. -/
theorem mixed_stationary_control_iff {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a]
    [DecidableEq a] [Fintype κ] [DecidableEq κ]
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (M : Set (Matrix a a ℂ)) (hM : ∀ ρa ∈ M, WildeQIT.IsDensityOperator ρa) :
    StationaryControlMixed H M ↔
      ∀ ρa ∈ M, (∀ α, α ≠ i0 → ∃ c : ℂ, coeffOp H F α * ρa = c • ρa) ∧
        HA H * ρa = ρa * HA H := by sorry

end BaconThesis.Control
