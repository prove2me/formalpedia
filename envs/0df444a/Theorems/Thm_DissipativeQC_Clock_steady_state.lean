-- Prove2me | Theorems.Thm_DissipativeQC_Clock_steady_state
-- name    : DissipativeQC.Clock.steady_state
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:42.860998+00:00
-- url     : https://prove2.me/theorems/4224e77b-9876-489d-80a8-22f539a25a02
-- title:
--   Eq. (4), p. 2 — the history state is stationary
-- statement:
--   For every number of qubits $N$, every circuit length $T$, and every family of unitary gates, the history matrix $\rho_0$ is a normalized positive semidefinite stationary state:
--
--   $$\mathcal L(\rho_0)=0,\qquad \rho_0\succeq0,\qquad \operatorname{tr}(\rho_0)=1.$$
--
--   This identifies the intended density matrix before uniqueness or spectral decay is considered.
--
--   **Formalization Note** The statement includes $N=0$ and $T=0$; the unitary gates are arbitrary on the qubit register. The clock transition uses the repaired indexing of equation (3).
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 2, eq. (4), "is a steady state, i.e. L(ρ0) = 0"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- Eq. (4): the history density matrix is stationary. -/
theorem steady_state (N T : ℕ)
    (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Qubits N) ℂ) :
    dqcGen U (rho0 U) = 0 ∧ (rho0 U).PosSemidef ∧ (rho0 U).trace = 1 := by sorry
end DissipativeQC.Clock
