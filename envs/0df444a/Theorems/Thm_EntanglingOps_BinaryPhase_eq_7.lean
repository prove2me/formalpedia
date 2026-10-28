-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_eq_7
-- name    : EntanglingOps.BinaryPhase.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:38.61103+00:00
-- url     : https://prove2.me/theorems/ed28a23d-6f02-469f-9f09-8fd1b3b42f43
-- title:
--   Eq. (7), p. 2 — d² tr_{A3B3}(ρ_{A3B3} P_{A2A3} P_{B2B3}) = ρ^T_{A2B2}
-- statement:
--   Let $d\ge1$ and let $A_2,A_3,B_2,B_3$ each be $\mathbb C^d$ with the basis $S=\{|i\rangle\}_{i=1}^d$. Let $P=|\Phi\rangle\langle\Phi|$ with $|\Phi\rangle=d^{-1/2}\sum_i|i\rangle|i\rangle$ (Eq. (5)), placed on $A_2A_3$ and on $B_2B_3$. For every operator $\rho$ on $A_3B_3$,
--
--   $$d^2\,\operatorname{tr}_{A_3B_3}\!\big(\rho_{A_3B_3}\,P_{A_2A_3}P_{B_2B_3}\big)=\rho^T_{A_2B_2},$$
--
--   where $\rho^T_{A_2B_2}$ is the same operator moved to $A_2B_2$ and transposed in the basis $S_{A_2}\otimes S_{B_2}$.
--
--   This is the step of the paper's proof of Eq. (6): a joint projection onto maximally entangled states moves an operator from one pair of systems to another, transposed.
--
--   Differences from the source:
--   - generalization: ρ_{A3B3} a state → every complex matrix ρ; reason: Eq. (7) is linear in ρ; states are a special case
--   - encoding: operators on ℋ_{A2}⊗ℋ_{B2}⊗ℋ_{A3}⊗ℋ_{B3}, basis |1⟩,…,|d⟩ → matrices indexed ((a2,b2),(a3,b3)) over Fin d; ρ_{A3B3} = 𝟙 ⊗ₖ ρ; tr_{A3B3} = partialTraceRight; reason: Lean carrier convention; same operators
--   - encoding: dimension d = dim ℋ with basis |1⟩,…,|d⟩ → hypothesis 0 < d on d : ℕ; reason: nondegeneracy only; a Hilbert space with the page's basis S has d ≥ 1, and at d = 0 every matrix is empty
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 2, Eq. (7)

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eq. (7), p. 2: `d² tr_{A₃B₃}(ρ_{A₃B₃} P_{A₂A₃} P_{B₂B₃}) = ρ^T_{A₂B₂}`. The carrier is indexed
`((a₂, b₂), (a₃, b₃))`; `ρ_{A₃B₃}` is `𝟙_{A₂B₂} ⊗ ρ`, `P_{A₂A₃} P_{B₂B₃}` is `projPhiPair d`,
`tr_{A₃B₃}` is `partialTraceRight`, and `ρᵀ` is the transpose in the product basis
`S_{A₂} ⊗ S_{B₂}`. Stated for every matrix `ρ`. -/
theorem eq_7 (d : ℕ) (hd : 0 < d) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
      (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d) = ρᵀ := by sorry

end EntanglingOps.BinaryPhase
