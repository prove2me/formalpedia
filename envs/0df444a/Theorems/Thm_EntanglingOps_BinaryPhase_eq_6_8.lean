-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_eq_6_8
-- name    : EntanglingOps.BinaryPhase.eq_6_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:19.061154+00:00
-- url     : https://prove2.me/theorems/62c08bd1-8c3b-43cc-bead-52ede3e067ae
-- title:
--   Eqs. (6) and (8), p. 2 — a CPM is recovered from its operator: ℰ(ρ) = d² tr_{A2B2}(E ρ^T) = d⁴ tr_{A2A3B2B3}(E ρ P P)
-- statement:
--   Let $d\ge1$, let each of $A_1,A_2,A_3,B_1,B_2,B_3$ be $\mathbb C^d$, and let $\mathcal E(\rho)=\sum_kO_k\rho O_k^\dagger$ be a completely positive map on $A_1B_1$ given by a finite family of Kraus operators. Let $E_{A_1A_2,B_1B_2}=\mathcal E(P_{A_1A_2}\otimes P_{B_1B_2})$ be its operator (Eq. (4)), with $P=|\Phi\rangle\langle\Phi|$ of Eq. (5). Then for every operator $\rho$:
--
--   1. (Eq. (8))
--   $$\mathcal E(\rho_{A_1B_1})=d^2\operatorname{tr}_{A_2B_2}\!\big(E_{A_1A_2,B_1B_2}\,\rho^T_{A_2B_2}\big);$$
--   2. (Eq. (6))
--   $$\mathcal E(\rho_{A_1B_1})=d^4\operatorname{tr}_{A_2A_3B_2B_3}\!\big(E_{A_1A_2,B_1B_2}\,\rho_{A_3B_3}\,P_{A_2A_3}P_{B_2B_3}\big).$$
--
--   Here $\rho_{A_1B_1}$, $\rho_{A_3B_3}$ and $\rho_{A_2B_2}$ denote the same operator on different pairs of systems, and $T$ is the transpose in the basis $S_{A_2}\otimes S_{B_2}$.
--
--   Equation (6) says that whoever holds the operator $E$ as a state can produce $\mathcal E$ on any input by a joint projection of $A_2A_3$ and $B_2B_3$ onto maximally entangled states; this is the mechanism of the paper's protocol.
--
--   Differences from the source:
--   - generalization: ρ a state → every complex matrix ρ; reason: both identities are linear in ρ; states are a special case
--   - encoding: a completely positive map ℰ on A1B1 → the map ρ ↦ ∑_k O_k ρ O_k† of a finite Kraus family O : κ → Matrix; reason: every CPM on a finite-dimensional space has a finite Kraus decomposition and every such family defines a CPM; same instances
--   - encoding: operators on the six systems → matrices on ((a1,b1),(a2,b2)) for (8) and on ((a1,b1),((a2,b2),(a3,b3))) for (6), via regroup and Equiv.prodAssoc; partial traces by partialTraceRight; reason: Lean carrier convention; same operators
--   - encoding: dimension d = dim ℋ with basis |1⟩,…,|d⟩ → hypothesis 0 < d on d : ℕ; reason: nondegeneracy only; a Hilbert space with the page's basis S has d ≥ 1, and at d = 0 every matrix is empty
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 2, Eqs. (6) and (8)

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eqs. (8) and (6), p. 2: a completely positive map `ℰ(ρ) = ∑_k O_k ρ O_k†` on `A₁B₁` is
recovered from its operator `E = choiOp O` of Eq. (4):
(8) `ℰ(ρ_{A₁B₁}) = d² tr_{A₂B₂}(E_{A₁A₂,B₁B₂} ρ^T_{A₂B₂})`, on the carrier `((a₁, b₁), (a₂, b₂))`;
(6) `ℰ(ρ_{A₁B₁}) = d⁴ tr_{A₂A₃B₂B₃}(E_{A₁A₂,B₁B₂} ρ_{A₃B₃} P_{A₂A₃} P_{B₂B₃})`, on the carrier
`((a₁, b₁), ((a₂, b₂), (a₃, b₃)))`. In both, `ρ` on the right is the same matrix as on the left,
placed on `A₂B₂` (transposed) or `A₃B₃`. Stated for every matrix `ρ`. -/
theorem eq_6_8 (d : ℕ) (hd : 0 < d) {κ : Type} [Fintype κ]
    (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    krausMap O ρ = ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
        (reindex (regroup d) (regroup d) (choiOp O) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρᵀ)) ∧
    krausMap O ρ = ((d : ℂ) ^ 4) • WildeQIT.partialTraceRight
        (reindex (Equiv.prodAssoc (Fin d × Fin d) (Fin d × Fin d) (Fin d × Fin d))
            (Equiv.prodAssoc (Fin d × Fin d) (Fin d × Fin d) (Fin d × Fin d))
            (reindex (regroup d) (regroup d) (choiOp O) ⊗ₖ
              (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d))) := by sorry

end EntanglingOps.BinaryPhase
