-- Prove2me | Theorems.Thm_DissipativeQC_Clock_identity_gap
-- name    : DissipativeQC.Clock.identity_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:32.049098+00:00
-- url     : https://prove2.me/theorems/2623cfd4-87f9-4406-927d-448478265cb0
-- title:
--   Appendix p. 5 (corrected: T ≥ 5) — DQC spectral gap for identity gates
-- statement:
--   For any $N$ and $T\ge5$, take the DQC generator with identity gates. Every nonzero complex eigenvalue $\mu$ obeys
--
--   $$\operatorname{Re}(\mu)<-\frac1{T^2}.$$
--
--   This assembles the clock block estimates into the generator's corrected spectral bound before allowing arbitrary circuit gates.
--
--   **Formalization Note** Direct diagonalization shows the printed bound fails for $T=1,2,3,4$. There is no lower bound on $N$. The gap is stated pointwise, with no default valued infimum.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 5, Appendix: Efficiency of DQC, "the gap of the Liouvillian is larger than 1/T²"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- Appendix p. 5, corrected to T at least five. -/
theorem identity_gap (N T : ℕ) (hT : 5 ≤ T) :
    ∀ μ : ℂ,
      (dqcGen (fun _ : Fin T => (1 : Matrix (Qubits N) (Qubits N) ℂ))).HasEigenvalue μ →
      μ ≠ 0 → μ.re < -1 / (T : ℝ) ^ 2 := by sorry
end DissipativeQC.Clock
