-- Prove2me | Theorems.Thm_DissipativeQC_Clock_unique_fixed_point
-- name    : DissipativeQC.Clock.unique_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:15.401659+00:00
-- url     : https://prove2.me/theorems/85afc205-71a7-41d2-bc4b-9dd5fc4b1994
-- title:
--   Appendix p. 5 (corrected: T ≥ 2) — identity gates have one stationary direction
-- statement:
--   For $N$ qubits, identity circuit gates, and $T\ge2$, every stationary matrix is a scalar multiple of the history state:
--
--   $$\ker(\mathcal L_I)=\mathbb C\rho_0.$$
--
--   This is the full zero eigenspace statement used to establish uniqueness of the stationary density matrix.
--
--   **Formalization Note** The bound $T\ge2$ corrects the printed unrestricted assertion: at $T=1$ a clock coherence is a second independent fixed matrix. $N=0$ is included.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 5, Appendix: Efficiency of DQC, "The only matrix with eigenvalue 0"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- Appendix p. 5: the zero eigenspace at identity gates is one-dimensional. -/
theorem unique_fixed_point (N T : ℕ) (hT : 2 ≤ T) :
    ∀ X : Matrix (Sys N T) (Sys N T) ℂ,
      dqcGen (fun _ : Fin T => (1 : Matrix (Qubits N) (Qubits N) ℂ)) X = 0 →
      ∃ c : ℂ, X = c • rho0 (fun _ : Fin T => (1 : Matrix (Qubits N) (Qubits N) ℂ)) := by sorry
end DissipativeQC.Clock
