-- Prove2me | Theorems.Thm_BaconThesis_Control_pure_stationary_control_iff
-- name    : BaconThesis.Control.pure_stationary_control_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:49.554112+00:00
-- url     : https://prove2.me/theorems/9dbbf781-505f-4c4f-9468-19ee5d2fcd8f
-- title:
--   §3.2.1 — pure state stationary control holds iff every $|a\rangle$ is an eigenvector of every $A_\alpha$ and of $H_A$ (3.4)
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on $\mathcal H_S\otimes\mathcal H_A$, $(F_\alpha)$ a fixed basis of the system operators with $F_0 = I/\sqrt d$, and $A_\alpha$, $H_A$ the operators of the expansion
--   $$
--   H = I_S\otimes H_A + \sum_{\alpha\neq0}F_\alpha\otimes A_\alpha .
--   $$
--   For a set $\mathcal A$ of apparatus vectors, $H$ performs pure state stationary control for $\mathcal A$ (condition (3.2)) if and only if for every $|a\rangle\in\mathcal A$
--   $$
--   A_\alpha|a\rangle = c_{\alpha,a}|a\rangle\quad(\alpha\neq0),\qquad H_A|a\rangle = \lambda_a|a\rangle \tag{3.4}
--   $$
--   for some numbers $c_{\alpha,a}$, $\lambda_a$.
--
--   The criterion reduces a condition on the dynamics for all times and all system states to an eigenvector condition on finitely many apparatus operators.
--
--   **Formalization Note** The zero vector satisfies both sides trivially.
--
--   Differences from the source:
--   - generalization: an orthogonal set 𝒜 of pure states → any set of apparatus vectors; reason: neither orthogonality nor normalization is used (the zero vector satisfies both sides); the book's sets are instances
--   - encoding: eigenvalues c_{α,a}, λ_a → complex numbers; reason: for Hermitian A_α, H_A they are automatically real on nonzero vectors; same instances
--   - encoding: A_α and H_A given by the expansion (3.3) → A_α = Tr_S[(F_α ⊗ I)H] and H_A = Tr_S[H]/d; reason: for a trace-orthonormal Hermitian basis these are the unique operators of (3.3); same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, eq. (3.4) and (3.6)–(3.9), pp.32–33 (PDF pp.49–50)

import Mathlib
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA
import Definitions.Def_BaconThesis_Control_StationaryControlPure

open scoped Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, eq. (3.4) and the necessity argument (3.6)–(3.9), pp.32–33 (PDF pp.49–50): "a sufficient
condition for pure state stationary control to hold is Aα|a⟩ = cα,a|a⟩ HA|a⟩ = λa|a⟩, (3.4) for
all |a⟩", and "Eq. (3.4) is also a necessary condition". For a Hermitian `H`, a fixed basis `F`
(index `i0` for `α = 0`) and a set `A` of apparatus vectors, `H` performs pure state stationary
control for `A` iff every `|a⟩ ∈ A` is an eigenvector of every `A_α`, `α ≠ 0`, and of `H_A`.

**Formalization Note.** `A_α = coeffOp H F α`, `H_A = HA H`; eigenvalues are complex numbers (the
zero vector counts as an eigenvector, for which both sides hold trivially). The book's `A` is an
orthogonal set of unit vectors; neither orthogonality nor normalization is assumed here. -/
theorem pure_stationary_control_iff {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a]
    [DecidableEq a] [Fintype κ] [DecidableEq κ]
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0) (A : Set (a → ℂ)) :
    StationaryControlPure H A ↔
      ∀ v ∈ A, (∀ α, α ≠ i0 → ∃ c : ℂ, coeffOp H F α *ᵥ v = c • v) ∧
        ∃ lam : ℂ, HA H *ᵥ v = lam • v := by sorry

end BaconThesis.Control
