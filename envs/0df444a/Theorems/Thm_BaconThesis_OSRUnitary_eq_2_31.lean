-- Prove2me | Theorems.Thm_BaconThesis_OSRUnitary_eq_2_31
-- name    : BaconThesis.OSRUnitary.eq_2_31
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:43.373177+00:00
-- url     : https://prove2.me/theorems/4440bec5-da13-4c83-bdea-478cc3d96e3f
-- title:
--   Eq. (2.31) — an OSR fixing every state has $\sum_i |\langle\psi|\tilde A_i|\psi\rangle|^2 = 1$
-- statement:
--   Let $(\tilde A_i)_{i\in\iota}$ be a finite family of $d\times d$ complex matrices whose operator-sum representation fixes every state:
--
--   $$
--   \sum_{i\in\iota} \tilde A_i\,\rho\,\tilde A_i^\dagger = \rho \qquad\text{for every density matrix } \rho .
--   $$
--
--   Then for every unit vector $\psi\in\mathbb C^d$,
--
--   $$
--   \sum_{i\in\iota} \bigl|\langle\psi|\tilde A_i|\psi\rangle\bigr|^2 = 1 .
--   $$
--
--   This is the first step of the thesis's proof that an OSR describing a unitary evolution consists of scalar multiples of the unitary: applied with $\rho = |\psi\rangle\langle\psi|$ to $\tilde A_i = U^\dagger A_i$.
--
--   **Formalization Note** "For all $\rho$" ranges over density matrices (positive semidefinite, trace one; the published `WildeQIT.IsDensityOperator`). A ket is a vector $\psi$ with $\langle\psi|\psi\rangle = 1$.
--
--   Differences from the source:
--   - generalization: Ã_i = U†A_i for an OSR {A_i} and a unitary U → any finite family Ã_i of matrices; reason: the step uses only (2.30); the book's case is At i = Uᴴ * A i
--   - reading: (2.30) "must hold for all ρ" → for every density matrix ρ; reason: the book's ρ are states; density matrices span all matrices and both sides are linear in ρ, so the readings are equivalent
--   - encoding: the state |ψ⟩ → a vector ψ with star ψ ⬝ᵥ ψ = 1; reason: ρ = |ψ⟩⟨ψ| must be a state, so |ψ⟩ is normalized; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.4, eqs. (2.30)–(2.31), p.19 (PDF p.36)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_OSRUnitary_osrApply

open scoped Matrix

namespace BaconThesis.OSRUnitary

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.4, eqs. (2.30)–(2.31), p.19 (PDF p.36): if the OSR `{Ã_i}` fixes every state,
`∑_i Ã_i ρ Ã_i† = ρ` (2.30), then for every unit vector `ψ`,
`∑_i |⟨ψ|Ã_i|ψ⟩|² = 1` (2.31).

**Formalization Note.** `Ã_i = U†A_i` of the book is an arbitrary family `At : ι → Matrix d d ℂ`
here (the step uses only (2.30)). "For all `ρ`" ranges over density operators
(`WildeQIT.IsDensityOperator`). A ket `|ψ⟩` is a vector `ψ : d → ℂ` with `⟨ψ|ψ⟩ = 1`, written
`star ψ ⬝ᵥ ψ = 1`, and `⟨ψ|Ã_i|ψ⟩ = star ψ ⬝ᵥ (At i *ᵥ ψ)`. -/
theorem eq_2_31 {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (At : ι → Matrix d d ℂ)
    (hfix : ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → osrApply At ρ = ρ)
    (ψ : d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∑ i, ‖star ψ ⬝ᵥ (At i *ᵥ ψ)‖ ^ 2 = 1 := by sorry

end BaconThesis.OSRUnitary
