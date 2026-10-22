-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_phase_reduction
-- name    : CliffordTApprox.Ancilla.phase_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:43.107451+00:00
-- url     : https://prove2.me/theorems/e251744c-5d64-48c1-b613-74cef7b70e2d
-- title:
--   §2.1, p. 3 — without loss of generality 0 ≤ φ ≤ π/4: Λ(e^{iφ}) = T^m Λ(e^{iφ'}) with m < 8 and φ' ∈ [0, π/4]
-- statement:
--   Let $T = \mathrm{diag}(1, e^{i\pi/4})$ be the T gate and $\Lambda(e^{i\varphi}) = \mathrm{diag}(1, e^{i\varphi})$. For every real $\varphi$ there are an integer $0 \le m < 8$ and a real $\varphi'$ with $0 \le \varphi' \le \pi/4$ such that
--   $$\Lambda(e^{i\varphi}) = T^m\,\Lambda(e^{i\varphi'}).$$
--
--   This makes exact the paper's "without loss of generality we can assume that $0 \le \varphi \le \pi/4$": a phase gate with any angle is a phase gate with angle in $[0,\pi/4]$ followed by at most seven T gates.
--
--   **Formalization Note.** The equality is between exact complex matrices on a one-qubit register; $T^m$ is a matrix power.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 3, §2.1

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.1, p. 3 ("without loss of generality 0 ≤ φ ≤ π/4"): every phase gate is an exact
power `T^m` (`m < 8`) of the T gate times a phase gate with angle in `[0, π/4]`. -/
theorem phase_reduction (φ : ℝ) :
    ∃ m : ℕ, m < 8 ∧ ∃ φ' : ℝ, 0 ≤ φ' ∧ φ' ≤ Real.pi / 4 ∧
      phaseGate φ = oneQubit gateT ^ m * phaseGate φ' := by sorry

end CliffordTApprox.Ancilla
