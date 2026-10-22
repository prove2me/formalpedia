-- Prove2me | Theorems.Thm_DissipativeQC_Clock_gate_removal
-- name    : DissipativeQC.Clock.gate_removal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:13.918989+00:00
-- url     : https://prove2.me/theorems/511dc12a-20b0-433c-b2e2-c9108062798a
-- title:
--   Appendix p. 4 — W removes the circuit gates and preserves the spectrum
-- statement:
--   Let $W=\sum_{t=0}^T U_t\cdots U_1\otimes|t\rangle\langle t|$ for a circuit of unitary gates. Then $W$ is unitary. Writing $\mathcal L_U$ for its DQC generator and $\mathcal L_I$ for the same generator with identity gates, one has
--
--   $$\mathcal L_U(WXW^\dagger)=W\mathcal L_I(X)W^\dagger$$
--
--   for every matrix $X$. Consequently $\mathcal L_U$ and $\mathcal L_I$ have exactly the same complex eigenvalues. This isolates the circuit independent part of the spectral question.
--
--   **Formalization Note** The quantification includes every $N,T$ and arbitrary unitary gates. Lean numbers gates from zero, so its $U(t)$ is the paper's $U_{t+1}$.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 4, Appendix: Efficiency of DQC, "First, we apply the unitary W"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- Appendix p. 4: W removes the circuit gates and preserves the spectrum. -/
theorem gate_removal (N T : ℕ)
    (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Qubits N) ℂ) :
    gateRemoval U ∈ Matrix.unitaryGroup (Sys N T) ℂ ∧
    (∀ X : Matrix (Sys N T) (Sys N T) ℂ,
      dqcGen U (gateRemoval U * X * (gateRemoval U)ᴴ) =
        gateRemoval U * dqcGen (fun _ : Fin T => (1 : Matrix (Qubits N) (Qubits N) ℂ)) X * (gateRemoval U)ᴴ) ∧
    (∀ μ : ℂ, (dqcGen U).HasEigenvalue μ ↔
      (dqcGen (fun _ : Fin T => (1 : Matrix (Qubits N) (Qubits N) ℂ))).HasEigenvalue μ) := by sorry
end DissipativeQC.Clock
