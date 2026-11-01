-- Prove2me | Theorems.Thm_BaconThesis_OSRUnitary_eq_2_35
-- name    : BaconThesis.OSRUnitary.eq_2_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:06.652711+00:00
-- url     : https://prove2.me/theorems/804c2afe-961c-4e58-a4ac-e56f1d6d245a
-- title:
--   Eq. (2.35) — if every state is an eigenstate of every $U^\dagger A_i$, then $A_i = c_i U$
-- statement:
--   Let $U$ be a $d\times d$ unitary matrix and $(A_i)_{i\in\iota}$ a finite family of $d\times d$ complex matrices, and put $\tilde A_i = U^\dagger A_i$. Suppose every unit vector $\psi\in\mathbb C^d$ is an eigenvector of every $\tilde A_i$: for each $i$ and each such $\psi$ there is a scalar $c$ (which may depend on $\psi$) with $\tilde A_i\psi = c\,\psi$. Then there are scalars $c_i\in\mathbb C$ with
--
--   $$
--   \tilde A_i = c_i I \quad\Longrightarrow\quad A_i = c_i U \qquad\text{for all } i .
--   $$
--
--   This is the last step of the thesis's proof of the §2.2.4 characterization: a common eigenvector property holding for all states forces each $\tilde A_i$ to be a multiple of the identity.
--
--   **Formalization Note** $U$ is unitary in the sense of Mathlib's `Matrix.unitaryGroup` ($U^\dagger U = UU^\dagger = I$). A ket is a vector $\psi$ with $\langle\psi|\psi\rangle = 1$. The conclusion states both $U^\dagger A_i = c_i I$ and $A_i = c_i U$ with the same $c_i$.
--
--   Differences from the source:
--   - encoding: every possible |ψ⟩ in the Hilbert space → every vector ψ with star ψ ⬝ᵥ ψ = 1; reason: states are normalized kets; a nonzero vector is a scalar multiple of a unit one, so the eigenvector property is the same
--   - encoding: U unitary (U†U = I of (2.28)) → U ∈ Matrix.unitaryGroup d ℂ; reason: in finite dimension U†U = I implies UU† = I; same instances
--   - generalization: A_i OSR operators of (2.11) satisfying (2.28) → any finite family A : ι → Matrix d d ℂ, without Σ_i A_i†A_i = I; reason: the step uses only the eigenvector property and U†U = I; the book's OSR is one instance
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.4, eq. (2.35), p.20 (PDF p.37)

import Mathlib

open scoped Matrix

namespace BaconThesis.OSRUnitary

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.4, eq. (2.35), p.20 (PDF p.37): if, for a unitary `U` and an OSR `{A_i}`, every unit vector
`ψ` is an eigenstate of every `Ã_i = U†A_i`, then `Ã_i = c_i I`, hence `A_i = c_i U`.

**Formalization Note.** The eigenvalue in the hypothesis may depend on `ψ` (as in the book,
where `c_i = ⟨ψ|Ã_i|ψ⟩`); the conclusion gives one scalar `c_i` per OSR operator. A ket is a
vector `ψ : d → ℂ` with `star ψ ⬝ᵥ ψ = 1`; `U† = Uᴴ`; `U ∈ Matrix.unitaryGroup d ℂ`. -/
theorem eq_2_35 {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (A : ι → Matrix d d ℂ) (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (heig : ∀ i, ∀ ψ : d → ℂ, star ψ ⬝ᵥ ψ = 1 → ∃ c : ℂ, (Uᴴ * A i) *ᵥ ψ = c • ψ) :
    ∃ c : ι → ℂ, ∀ i, Uᴴ * A i = c i • (1 : Matrix d d ℂ) ∧ A i = c i • U := by sorry

end BaconThesis.OSRUnitary
