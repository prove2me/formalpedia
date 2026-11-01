-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_uhlmann
-- name    : BenyOreshkov.AQEC.uhlmann
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:20:59.479157+00:00
-- url     : https://prove2.me/theorems/c90ed8e8-e12c-44f9-a33f-e2fcdf646dce
-- title:
--   Proof of Theorem 1, p. 2 — Uhlmann's theorem, the fidelity is the largest overlap $|\langle\psi|(1\otimes C)|\varphi\rangle|$ over contractions
-- statement:
--   Let $X$, $Y$, $Y'$ be finite-dimensional Hilbert spaces, $|\psi\rangle\in X\otimes Y$ and $|\varphi\rangle\in X\otimes Y'$ (not necessarily normalized), and let $\rho=\mathrm{Tr}_Y|\psi\rangle\langle\psi|$ and $\sigma=\mathrm{Tr}_{Y'}|\varphi\rangle\langle\varphi|$. Then
--   $$
--   f(\rho,\sigma)=\mathrm{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho} = \max_{C : Y'\to Y,\ \|C\|\le 1}\ \big|\langle\psi|(1_X\otimes C)|\varphi\rangle\big|,
--   $$
--   and the maximum over operators $C$ of operator norm at most one is attained. This is Uhlmann's theorem in the form used in the proof of Theorem 1: the entanglement fidelity is an overlap of purifications maximized over the purifying system, and "the max over $U'$ can also be taken over operators $A'$ in the unit ball".
--
--   **Formalization Note** The overlap is $\sum_{x,y,y'}\overline{\psi_{x y}}\,C_{y y'}\,\varphi_{x y'}$, and $\|C\|\le1$ is written $C^\dagger C\le 1$ in the Loewner order.
--
--   Differences from the source:
--   - encoding: maximum over unitaries U′ on a common purifying space → maximum over contractions C : Y′ → Y between purifying spaces of arbitrary dimensions; reason: the purifying systems of the proof (E ⊗ K and E′) differ in dimension; the source itself passes to the unit ball on p. 2; the maximum value is the same
--   - generalization: purifications of states → arbitrary, not necessarily normalized vectors; reason: both sides scale the same way; normalized vectors are the source's case
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, proof of Theorem 1, p. 2 (Uhlmann's theorem [23]; unit-ball remark)

import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_partialTrace

open Matrix QAlgorithms WildeQIT
open scoped MatrixOrder

namespace BenyOreshkov.AQEC

/-- **Uhlmann's theorem, contraction form.** Bény, Oreshkov, arXiv:0907.5391v4, proof of
Theorem 1, p. 2 ("applying Uhlmann's theorem [23] which allows us to write the entanglement
fidelity in terms of an overlap maximized over unitary operators U′", and "the max over U′ can
also be taken over operators A′ in the unit ball"). For vectors `ψ ∈ ℂ^X ⊗ ℂ^Y` and
`φ ∈ ℂ^X ⊗ ℂ^{Y′}`, the root fidelity of their reduced operators on `X` is the largest overlap
`|⟨ψ|(1_X ⊗ C)|φ⟩|` over contractions `C : Y′ → Y`, and the largest value is attained.

**Formalization Note** `|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)` and the reduction is the partial trace
over the second factor. The vectors need not be normalized, and the purifying systems `Y`, `Y′`
may differ, which is why contractions (`Cᴴ * C ≤ 1`, i.e. operator norm at most 1) replace the
unitaries of the paper (Reading 8). -/
theorem uhlmann {X Y Y' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y'] (ψ : X × Y → ℂ) (φ : X × Y' → ℂ) :
    IsGreatest
      {t : ℝ | ∃ C : Matrix Y Y' ℂ, Cᴴ * C ≤ 1 ∧
        t = ‖∑ x, ∑ y, ∑ y', star (ψ (x, y)) * C y y' * φ (x, y')‖}
      (rootFidelity (partialTraceRight (vecMulVec ψ (star ψ)))
        (partialTraceRight (vecMulVec φ (star φ)))) := by sorry

end BenyOreshkov.AQEC
