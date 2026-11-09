-- Prove2me | Theorems.Thm_CliffordCert_Optimal_clifford_realization
-- name    : CliffordCert.Optimal.clifford_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:49:07.449231+00:00
-- url     : https://prove2.me/theorems/2563bb45-fa02-4db1-bbca-a0444e3c7eb4
-- title:
--   Lemma 4 — Clifford realization of the retained subspace
-- statement:
--   Let $1\le q\le n$ and let $S\subseteq\mathbb F_2^n\oplus\mathbb F_2^n$ be nondegenerate of dimension $2q$. There is a Clifford unitary $C_S$ on the original $n$ qubits such that
--   $$C_SP_vC_S^\dagger\text{ acts as identity on the last }n-q\text{ qubits}\quad\Longleftrightarrow\quad v\in S.$$
--   For labels in $S$, the images are signed retained Paulis tensored with the discarded identity, and every retained Pauli occurs modulo sign.
--
--   Both the equivalence and exhaustion clause are included, providing the physical realization of a retained symplectic subspace.
--
--   Differences from the source:
--   - encoding: n-qubit matrices and labelled tensor registers → matrices indexed by Fin n → Fin 2 and tensor configurations indexed by finite functions; reason: these are the computational bases, with the first q qubits retained and the last n−q discarded
--   - encoding: identity on the discarded subsystem → membership in the range A ↦ A ⊗ I, with the stated tensor order; reason: this is exactly the source condition, including when no qubit is discarded
--   - encoding: field-valued binary labels and Clifford matrices → published signed Pauli and individual Clifford definitions with Fin 2 label and bundled-unitary adapters; reason: binary residues 0 and 1 preserve the Eq. (18) phase and tensor order; the Clifford predicate requires every list member, with no random weights
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 12, Lemma 4 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clifford_realization {n q : ℕ} (hq : 1 ≤ q) (hqn : q ≤ n)
    (S : Submodule F₂ (Label n)) (hS : LabelNondegenerate S)
    (hdim : Module.finrank F₂ S = 2*q) :
    ∃ C : Mat (Bits n), IsClifford C ∧
      (∀ v : Label n, ActsOnlyOnRetained hqn (C * pauli v * Cᴴ) ↔ v ∈ S) ∧
      (∀ v ∈ S, ∃ w : Label q, ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        C * pauli v * Cᴴ = (sign : ℂ) • retainedLift hqn (pauli w)) ∧
      (∀ w : Label q, ∃ v ∈ S, ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        C * pauli v * Cᴴ = (sign : ℂ) • retainedLift hqn (pauli w)) := by sorry
end CliffordCert.Optimal
