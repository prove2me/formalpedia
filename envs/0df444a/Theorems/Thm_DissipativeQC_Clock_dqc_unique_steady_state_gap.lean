-- Prove2me | Theorems.Thm_DissipativeQC_Clock_dqc_unique_steady_state_gap
-- name    : DissipativeQC.Clock.dqc_unique_steady_state_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:33.508446+00:00
-- url     : https://prove2.me/theorems/c79daefc-cbd4-4809-bf9e-388cc2cdb404
-- title:
--   pp. 2, 5 (corrected: T ≥ 2, gap for T ≥ 5) — unique history state and spectral bound
-- statement:
--   For every $N$, every circuit length $T\ge2$, and every family of unitary gates, the DQC history matrix $\rho_0$ is a normalized positive semidefinite stationary state, and the whole stationary space is its complex span. When $T\ge5$, each nonzero eigenvalue $\mu$ of the generator satisfies
--
--   $$\mathcal L(\rho_0)=0,\quad \rho_0\succeq0,\quad \operatorname{tr}(\rho_0)=1,\quad \ker\mathcal L=\mathbb C\rho_0,\quad \operatorname{Re}(\mu)<-\frac1{T^2}.$$
--
--   The result identifies the intended steady state and gives a circuit independent spectral scale for relaxation.
--
--   **Formalization Note** Uniqueness needs $T\ge2$ because it fails at $T=1$; the strict gap bound needs $T\ge5$ because it fails below that threshold. The printed exact gap value is not asserted: the slowest one sided coherence has a corner coefficient $-3/2$. The gates are arbitrary unitaries rather than nearest neighbor gates, $N=0$ is allowed, and the step operator uses $U_{t+1}$ on the transition $t\to t+1$ to repair equation (3).
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 2, eq. (4) and claim after it; p. 5, Appendix: Efficiency of DQC, "the gap of the Liouvillian is larger than 1/T²"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- DQC steady state, uniqueness, and corrected spectral-gap bound. -/
theorem dqc_unique_steady_state_gap (N T : ℕ) (hT : 2 ≤ T)
    (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Qubits N) ℂ) :
    (dqcGen U (rho0 U) = 0 ∧ (rho0 U).PosSemidef ∧ (rho0 U).trace = 1) ∧
    (∀ X : Matrix (Sys N T) (Sys N T) ℂ,
      dqcGen U X = 0 → ∃ c : ℂ, X = c • rho0 U) ∧
    (5 ≤ T → ∀ μ : ℂ, (dqcGen U).HasEigenvalue μ → μ ≠ 0 →
      μ.re < -1 / (T : ℝ) ^ 2) := by sorry
end DissipativeQC.Clock
