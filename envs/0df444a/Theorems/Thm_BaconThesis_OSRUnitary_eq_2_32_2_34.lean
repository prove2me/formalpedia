-- Prove2me | Theorems.Thm_BaconThesis_OSRUnitary_eq_2_32_2_34
-- name    : BaconThesis.OSRUnitary.eq_2_32_2_34
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:58:51.815808+00:00
-- url     : https://prove2.me/theorems/1b3f358d-f0a4-4ade-820f-2072b558f328
-- title:
--   Eqs. (2.32)–(2.34) — every unit $\psi$ with $\sum_i |\langle\psi|\tilde A_i|\psi\rangle|^2 = 1$ is a common eigenvector
-- statement:
--   Let $(\tilde A_i)_{i\in\iota}$ be a finite family of $d\times d$ complex matrices with
--
--   $$
--   \sum_{i\in\iota} \tilde A_i^\dagger \tilde A_i = I ,
--   $$
--
--   and let $\psi\in\mathbb C^d$ be a unit vector with $\sum_i |\langle\psi|\tilde A_i|\psi\rangle|^2 = 1$. Write $\tilde A_i|\psi\rangle = c_i|\psi\rangle + c_i^\perp|\psi^\perp\rangle$ with $|\psi^\perp\rangle\perp|\psi\rangle$, so that $c_i = \langle\psi|\tilde A_i|\psi\rangle$. Then every perpendicular component vanishes: $\psi$ is an eigenvector of every $\tilde A_i$,
--
--   $$
--   \tilde A_i|\psi\rangle = c_i\,|\psi\rangle ,\qquad c_i = \langle\psi|\tilde A_i|\psi\rangle ,\qquad\text{for all } i .
--   $$
--
--   This is the middle step of the thesis's proof of the §2.2.4 characterization: (2.31) and the normalization (2.33) together leave no room for components of $\tilde A_i\psi$ orthogonal to $\psi$.
--
--   **Formalization Note** The normalization is the definition `IsTracePreservingOSR`. A ket is a vector $\psi$ with $\langle\psi|\psi\rangle = 1$, and $\langle\psi|\tilde A_i|\psi\rangle$ is `star ψ ⬝ᵥ (At i *ᵥ ψ)`.
--
--   Differences from the source:
--   - generalization: Ã_i = U†A_i for an OSR {A_i} with (2.28) and a unitary U → any finite family Ã_i with Σ Ã_i†Ã_i = I; reason: the step uses only (2.31) and (2.33); the book's case is At i = Uᴴ * A i
--   - encoding: the state |ψ⟩ → a vector ψ with star ψ ⬝ᵥ ψ = 1; reason: ρ = |ψ⟩⟨ψ| must be a state, so |ψ⟩ is normalized; same instances
--   - encoding: c_i, the component of Ã_i|ψ⟩ along |ψ⟩ → the explicit value ⟨ψ|Ã_i|ψ⟩; reason: for a unit ψ the component along ψ in the split Ã_i|ψ⟩ = c_i|ψ⟩ + c_i^⊥|ψ^⊥⟩ is ⟨ψ|Ã_i|ψ⟩; same statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.4, eqs. (2.32)–(2.34) and the sentence after (2.34), p.20 (PDF p.37)

import Mathlib
import Definitions.Def_BaconThesis_OSRUnitary_IsTracePreservingOSR

open scoped Matrix

namespace BaconThesis.OSRUnitary

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.4, eqs. (2.32)–(2.34) and the sentence after them, p.20 (PDF p.37): if
`∑_i Ã_i† Ã_i = I` (2.33) and `∑_i |⟨ψ|Ã_i|ψ⟩|² = 1` (2.31) for a unit vector `ψ`, then `ψ` is an
eigenstate of every `Ã_i`, `Ã_i|ψ⟩ = c_i|ψ⟩`, where `c_i = ⟨ψ|Ã_i|ψ⟩` is the component of
`Ã_i|ψ⟩` along `|ψ⟩` (so the perpendicular components `c_i^⊥` all vanish).

**Formalization Note.** `Ã_i` is an arbitrary family `At : ι → Matrix d d ℂ`, (2.33) is
`IsTracePreservingOSR At`. A ket is a vector `ψ : d → ℂ` with `star ψ ⬝ᵥ ψ = 1`;
`⟨ψ|Ã_i|ψ⟩ = star ψ ⬝ᵥ (At i *ᵥ ψ)`. The eigenvalue is named explicitly as the book's `c_i`. -/
theorem eq_2_32_2_34 {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (At : ι → Matrix d d ℂ) (hnorm : IsTracePreservingOSR At)
    (ψ : d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (h231 : ∑ i, ‖star ψ ⬝ᵥ (At i *ᵥ ψ)‖ ^ 2 = 1) :
    ∀ i, At i *ᵥ ψ = (star ψ ⬝ᵥ (At i *ᵥ ψ)) • ψ := by sorry

end BaconThesis.OSRUnitary
