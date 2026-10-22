-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_main_result
-- name    : CliffordTApprox.Ancilla.main_result
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:37.143123+00:00
-- url     : https://prove2.me/theorems/8aaedfd3-10d8-4bee-93d0-e4bb7bcd4b97
-- title:
--   Abstract and §2, pp. 1–4 — every single-qubit unitary within ε by O(log(1/ε)) H, T, CNOT gates and two |0⟩ ancillas
-- statement:
--   There is an absolute constant $A > 0$ such that for every $2\times2$ unitary matrix $U$ and every $0 < \varepsilon \le 1$ there is a circuit $C$ of gates from $\{H, T, \mathrm{CNOT}\}$ on three wires, the data qubit followed by two ancillas initialized to $|0\rangle$, such that
--   $$\big\|\,\psi\mapsto C(\psi\otimes|00\rangle)\ -\ \psi\mapsto(U\psi)\otimes|00\rangle\,\big\|_F \le \varepsilon \qquad\text{and}\qquad \#C \le A\left(\log_2\frac1\varepsilon + 1\right).$$
--
--   This is the paper's main result: single-qubit unitaries are approximated to precision $\varepsilon$ with $O(\log(1/\varepsilon))$ Clifford and T gates using two ancillary qubits, which matches the $\Omega(\log(1/\varepsilon))$ lower bound and improves on the $O(\log^{3+\delta}(1/\varepsilon))$ of the Solovay–Kitaev algorithm.
--
--   **Formalization Note.** The error is the Frobenius norm of the difference of two linear maps from one qubit to three qubits: it is sensitive to the global phase of $U$ and charges any amplitude left on the ancillas, and it dominates the per-state distance used on the page. "Up to two ancillary qubits" is formalized as exactly two ancilla wires (an unused one is idle). The gate set is $\{H, T, \mathrm{CNOT}\}$ ($S=T^2$, $X=HT^4H$). The page's $O(\log(1/\varepsilon))$ is pinned as $A(\log_2(1/\varepsilon)+1)$ with $A$ quantified before $U$ and $\varepsilon$; the $+1$ makes the bound meaningful for $\varepsilon$ near $1$.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 1, Abstract; §2, pp. 2–4

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- Abstract, p. 1; §2, pp. 2–4: there is an absolute constant `A` such that every single-qubit
unitary `U` is approximated to precision `ε ∈ (0, 1]` (Frobenius norm of the initialized map,
phase-sensitive, ancilla leakage charged) by an `{H, T, CNOT}` circuit on the data wire and two
ancillas initialized to `|0⟩`, with at most `A (log₂(1/ε) + 1)` gates. -/
theorem main_result :
    ∃ A : ℝ, 0 < A ∧ ∀ U : Matrix (Qubits 1) (Qubits 1) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : Circuit htcxGateSet (1 + 2),
        frobNorm (initializedMap c.unitary - idealMap U 2) ≤ ε ∧
        (c.size : ℝ) ≤ A * (Real.log (1 / ε) / Real.log 2 + 1) := by sorry

end CliffordTApprox.Ancilla
