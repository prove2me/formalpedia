-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_eq_10
-- name    : EntanglingOps.BinaryPhase.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:30.269815+00:00
-- url     : https://prove2.me/theorems/d69154af-8fd2-43ed-8c5b-029d76d87c83
-- title:
--   Eq. (10), p. 3 — the operator of U(α) is |ψ_α⟩⟨ψ_α|, with ψ_α = (U(α) ⊗ 𝟙)|Φ⁺⟩|Φ⁺⟩
-- statement:
--   Let $U(\alpha)=e^{-i\alpha\,\sigma_x^{A_1}\otimes\sigma_x^{B_1}}$ (Eq. (9)) and let
--
--   $$|\psi_\alpha\rangle=\cos\alpha\,|\Phi^+\rangle_{A_1A_2}|\Phi^+\rangle_{B_1B_2}-i\sin\alpha\,|\Psi^+\rangle_{A_1A_2}|\Psi^+\rangle_{B_1B_2}$$
--
--   be the state printed in Eq. (10), with the Bell states $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ and $|\Psi^+\rangle=(|01\rangle+|10\rangle)/\sqrt2$. Then for every real $\alpha$:
--
--   1. $|\psi_\alpha\rangle=(U(\alpha)_{A_1B_1}\otimes\mathbb 1_{A_2B_2})\,|\Phi^+\rangle_{A_1A_2}|\Phi^+\rangle_{B_1B_2}$;
--   2. the operator of Eq. (4) of the map $\rho\mapsto U(\alpha)\rho\,U(\alpha)^\dagger$ (qubits, $d=2$) is
--   $$E_{A_1A_2,B_1B_2}=|\psi_\alpha\rangle\langle\psi_\alpha|.$$
--
--   This identifies the resource state the protocol consumes: one copy of $|\psi_\alpha\rangle$ is exactly what Eq. (6) needs to implement $U(\alpha)$ probabilistically.
--
--   Differences from the source:
--   - generalization: α = α_N = π/2^N → every real α; reason: the identity holds for every phase; α = α_N is an instance
--   - encoding: 'the corresponding operator E' of U(α_N) → choiOp of the one-element Kraus family {U(α)} (at d = 2, where |Φ⟩ of (5) is |Φ⁺⟩); reason: the map ρ ↦ UρU† has the single Kraus operator U; same object
--   - encoding: state vectors on A1A2B1B2 → functions on ((a1,a2),(b1,b2)), identity 1 stated entrywise; reason: Lean carrier convention; same vectors
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, Eqs. (9)–(10)

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eq. (10), p. 3: the resource state of the printed formula (10) is the gate `U(α)` of (9) on
`A₁B₁` applied to `|Φ⁺⟩_{A₁A₂}|Φ⁺⟩_{B₁B₂}` (entrywise, at `((a₁, a₂), (b₁, b₂))`), and the
operator `E_{A₁A₂,B₁B₂}` of Eq. (4) of the map `ρ ↦ U(α) ρ U(α)†` is `|ψ_α⟩⟨ψ_α|`. Stated for
every real `α` (the paper's `α_N` is one instance). -/
theorem eq_10 :
    (∀ (α : ℝ) (x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)),
      resource α x = ∑ y : Fin 2 × Fin 2,
        gate α (x.1.1, x.2.1) y * phiPlus (y.1, x.1.2) * phiPlus (y.2, x.2.2)) ∧
    (∀ α : ℝ, choiOp (fun _ : Unit => gate α) = vecMulVec (resource α) (star (resource α))) := by sorry

end EntanglingOps.BinaryPhase
