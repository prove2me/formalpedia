-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_decomposition
-- name    : CliffordTApprox.Ancilla.decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:30.757017+00:00
-- url     : https://prove2.me/theorems/0de69b1d-f460-4ae9-806f-b966f98df4ed
-- title:
--   §2, p. 2 — every single-qubit unitary is a product of a constant number of Hadamard gates and phase gates Λ(e^{iθ})
-- statement:
--   Let $H = \frac{1}{\sqrt 2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ be the Hadamard gate and $\Lambda(e^{i\theta}) = \mathrm{diag}(1, e^{i\theta})$ the phase gate, and let $X = H\,\Lambda(e^{i\pi})\,H$ (the bit flip). For every $2\times 2$ unitary matrix $U$ there are real numbers $\theta, \varphi_1, \varphi_2, \varphi_3$ such that
--   $$U = \Lambda(e^{i\theta})\,X\,\Lambda(e^{i\theta})\,X\;\Lambda(e^{i\varphi_1})\,H\,\Lambda(e^{i\varphi_2})\,H\,\Lambda(e^{i\varphi_3}).$$
--   Thus every single-qubit unitary, including its global phase, is a product of seven phase gates and six Hadamard gates in a fixed pattern.
--
--   This is the reduction with which the paper passes from the phase gate $\Lambda(e^{i\varphi})$ to an arbitrary single-qubit unitary: an approximation of each phase gate gives an approximation of $U$.
--
--   **Formalization Note.** The equality is exact, between complex matrices on a one-qubit register; the factor $\Lambda(e^{i\theta})X\Lambda(e^{i\theta})X$ equals $e^{i\theta}I$ and carries the global phase. The paper cites the solution to Problem 8.1 of Kitaev–Shen–Vyalyi for this fact and gives no explicit pattern; the pattern above is one admissible choice.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 2, §2 (citing Problem 8.1 of Kitaev, Shen, Vyalyi)

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2, p. 2: every single-qubit unitary `U ∈ U(2)` (global phase included) is a product of
Hadamard gates `H` and phase gates `Λ(e^{iθ})`, with a fixed pattern of 7 phase gates and 6
Hadamards: `U = Λ(θ) X Λ(θ) X Λ(φ₁) H Λ(φ₂) H Λ(φ₃)` where `X = H Λ(e^{iπ}) H`. -/
theorem decomposition (U : Matrix (Qubits 1) (Qubits 1) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 1) ℂ) :
    ∃ θ φ₁ φ₂ φ₃ : ℝ,
      U = phaseGate θ * (oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard) *
        phaseGate θ * (oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard) *
        phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard * phaseGate φ₃ := by sorry

end CliffordTApprox.Ancilla
