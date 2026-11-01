-- Prove2me | Theorems.Thm_BaconThesis_OSRUnitary_osr_unitary_iff
-- name    : BaconThesis.OSRUnitary.osr_unitary_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:54.74351+00:00
-- url     : https://prove2.me/theorems/c4e3ddc2-4f9f-4253-8feb-0417b82836d3
-- title:
--   §2.2.4 — an OSR is the unitary evolution $U$ iff $A_i = c_i U$ with $\sum_i |c_i|^2 = 1$
-- statement:
--   Let $d$ be a finite, nonempty index set, $U$ a $d\times d$ unitary matrix, and $(A_i)_{i\in\iota}$ a finite family of $d\times d$ complex matrices (the OSR operators). The following are equivalent:
--
--   1. the operator-sum representation of the $A_i$ is the unitary evolution by $U$ and is normalized, that is,
--   $$
--   \sum_{i\in\iota} A_i\,\rho\,A_i^\dagger = U\rho\,U^\dagger \quad\text{for every density matrix } \rho \qquad\text{and}\qquad \sum_{i\in\iota} A_i^\dagger A_i = I ;
--   $$
--   2. every OSR operator is a scalar multiple of $U$: there are $c_i\in\mathbb C$ with
--   $$
--   A_i = c_i\,U \quad\text{for all } i, \qquad \sum_{i\in\iota} |c_i|^2 = 1 .
--   $$
--
--   This is the claim of §2.2.4 of the thesis, eqs. (2.27)–(2.28): it answers when an OSR, which in general describes decoherence, is in fact a unitary evolution, and it is the prototype of the decoherence-free conditions of the later chapters.
--
--   **Formalization Note** The system is $\mathbb C^d$ with $d$ a nonempty finite type, and the OSR index $\iota$ is any finite type, possibly empty. Unitarity of $U$ is Mathlib's `Matrix.unitaryGroup`. Density matrices are the published `WildeQIT.IsDensityOperator`; the OSR and its normalization are the definitions `osrApply` and `IsTracePreservingOSR`.
--
--   Differences from the source:
--   - encoding: a system Hilbert space of any dimension → a finite nonempty index type d; reason: for d empty the left side holds with an empty OSR while no c has Σ|c_i|² = 1; the hypothesis excludes only the zero-dimensional space, which the book does not consider
--   - reading: (2.27) "for all ρ" → for every density matrix ρ; reason: the book's ρ are states; density matrices span all matrices and both sides are linear in ρ, so the readings are equivalent
--   - reading: "(2.27), where U†U = Σ_i A_i†A_i = I (2.28)" → U†U = I is a standing hypothesis and the left side is (2.27) together with Σ_i A_i†A_i = I; reason: the book's proof reads both directions as "Eq. (2.27) and Eq. (2.28) both hold"; under Σ_i A_i†A_i = I the left side is (2.27) alone
--   - encoding: U unitary (U†U = I of (2.28)) → U ∈ Matrix.unitaryGroup d ℂ; reason: in finite dimension U†U = I implies UU† = I; same instances
--   - encoding: c_i(t) → c : ι → ℂ; reason: the A_i are taken at one fixed time t, so the c_i are scalars
--   - generalization: A_i the OSR operators √p_ν⟨μ|U(t)|ν⟩ of (2.11) → any finite family A : ι → Matrix d d ℂ; reason: the claim and its proof use only (2.27)–(2.28); every OSR of (2.11) is such a family
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.4, (2.27)–(2.28), p.19 (PDF p.36), proof to (2.35), p.20 (PDF p.37)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_OSRUnitary_osrApply
import Definitions.Def_BaconThesis_OSRUnitary_IsTracePreservingOSR

open scoped Matrix

namespace BaconThesis.OSRUnitary

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.4 "OSR and unitary evolution", (2.27)–(2.28), p.19 (PDF p.36), proof to (2.35), p.20
(PDF p.37): for a unitary `U`, the OSR `{A_i}` satisfies (2.27) `∑_i A_i ρ A_i† = U ρ U†` for
all `ρ` together with (2.28) `∑_i A_i† A_i = I` if and only if `A_i = c_i U` for scalars `c_i`
with `∑_i |c_i|² = 1`.

**Formalization Note.** The system is `d → ℂ` with `d` a finite, **nonempty** type (for an
empty `d` the left side holds with an empty OSR while no `c` has `∑ |c_i|² = 1`). The OSR index
`ι` is any finite type (possibly empty). `U ∈ Matrix.unitaryGroup d ℂ` is the standing
hypothesis `U†U = I` of (2.28). "For all `ρ`" ranges over density operators
(`WildeQIT.IsDensityOperator`: positive semidefinite, trace one). The book's `c_i(t)` are
scalars at the fixed time of the OSR, so `c : ι → ℂ`. -/
theorem osr_unitary_iff {d ι : Type} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype ι]
    (A : ι → Matrix d d ℂ) (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    ((∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → osrApply A ρ = U * ρ * Uᴴ) ∧
        IsTracePreservingOSR A) ↔
      ∃ c : ι → ℂ, (∀ i, A i = c i • U) ∧ ∑ i, ‖c i‖ ^ 2 = 1 := by sorry

end BaconThesis.OSRUnitary
