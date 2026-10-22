-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_phase_gate_approx
-- name    : CliffordTApprox.Ancilla.phase_gate_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:32.883618+00:00
-- url     : https://prove2.me/theorems/b2bbe84a-7e0c-41bb-a7aa-68d03d1f0f2c
-- title:
--   §2.2, p. 3 — Λ(e^{iφ}) is approximated within √(2/4^k + 2√2/2^k) by O(k) H, T, CNOT gates with two |0⟩ ancillas
-- statement:
--   There is an absolute constant $A>0$ such that for every $k\in\mathbb N$ and every real $\varphi$ there is a circuit $C$ of gates from $\{H, T, \mathrm{CNOT}\}$ on three wires (the data qubit, then two ancillas initialized to $|0\rangle$) with
--   $$\big\|\,\psi \mapsto C(\psi\otimes|00\rangle)\ -\ \psi\mapsto(\Lambda(e^{i\varphi})\psi)\otimes|00\rangle\,\big\|_F \le \sqrt{\frac{2}{4^k} + \frac{2\sqrt2}{2^k}} \quad\text{and}\quad \#C \le A\,(k+1).$$
--
--   This is the paper's main result for the phase gate: precision $O(1/2^{0.5k})$ with $O(k)$ gates, i.e. $O(\log(1/\varepsilon))$ gates for precision $\varepsilon$.
--
--   **Formalization Note.** The error is the Frobenius norm of the difference of the two linear maps from one qubit to three qubits; it is sensitive to the global phase and charges any amplitude left on the ancillas. The constants $\sqrt{2/4^k + 2\sqrt2/2^k}$ and $A(k+1)$ pin the page's $O(1/2^{0.5k})$ and $O(k)$; $A$ is quantified before $k$ and $\varphi$. The statement holds for every real $\varphi$, not only $0\le\varphi\le\pi/4$, through the reduction $\Lambda(e^{i\varphi}) = T^m\Lambda(e^{i\varphi'})$.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, pp. 2–3, §2 and §2.2

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.2, p. 3: for every `k` and every `φ` there is an `{H, T, CNOT}` circuit on the data wire and
two `|0⟩` ancillas, of size `O(k)` with an absolute constant, whose initialized map is within
Frobenius distance `√(2/4^k + 2√2/2^k)` of `Λ(e^{iφ}) ⊗ |00⟩`. -/
theorem phase_gate_approx :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (φ : ℝ), ∃ c : Circuit htcxGateSet (1 + 2),
      frobNorm (initializedMap c.unitary - idealMap (phaseGate φ) 2) ≤
        Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) ∧
      (c.size : ℝ) ≤ A * ((k : ℝ) + 1) := by sorry

end CliffordTApprox.Ancilla
