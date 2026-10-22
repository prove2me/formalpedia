-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_controlled_preparation
-- name    : CliffordTApprox.Ancilla.controlled_preparation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:24.376295+00:00
-- url     : https://prove2.me/theorems/03dc2622-ee87-41d4-9895-08e29ec1d48a
-- title:
--   §2.2, p. 3 and §2.3, p. 4 — a two-qubit state with entries in Z[i]/2^k is prepared, controlled, by O(k) H, T, CNOT gates with no further ancilla
-- statement:
--   There is an absolute constant $A > 0$ with the following property. Let $k\in\mathbb N$ and let $v$ be a unit vector of two qubits each of whose four entries has the form $(a+ib)/2^k$ with $a, b\in\mathbb Z$. Then there is a circuit $C$ of gates from $\{H, T, \mathrm{CNOT}\}$ on three wires (the data qubit and the two ancillas, and no other wire) such that
--   $$C|0\rangle|00\rangle = |0\rangle|00\rangle, \qquad C|1\rangle|00\rangle = |1\rangle|v\rangle, \qquad \#C \le A\,(k+1),$$
--   where $\#C$ is the number of gates.
--
--   This is the exact-synthesis step of the algorithm: the circuit that prepares $|v\rangle$ (Giles–Selinger's column lemma), taken controlled on the data qubit, with $O(k)$ gates and without a third ancilla. It is what makes two ancillas suffice in total.
--
--   **Formalization Note.** Each gate is $H$ or $T$ on one wire or CNOT on an ordered pair of distinct wires; $S = T^2$ and $X = HT^4H$, so the Clifford and T library differs from $\{H, T, \mathrm{CNOT}\}$ in gate counts by a constant factor only. The page writes $O(k)$; the constant $A$ is quantified before $k$ and $v$, so it does not depend on them, and the $+1$ covers $k = 0$. Entries are Gaussian integers over $2^k$, exactly as for the paper's $|v\rangle$. The page cites this step from Giles–Selinger (Lemma 20, Lemma 24) and from its reference [9] (Theorem 1).
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 3, §2.2 (citing Giles–Selinger Lemma 20 and [9] Theorem 1) and p. 4, §2.3 (citing Giles–Selinger Lemma 24)

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.2, p. 3 and §2.3, p. 4: every unit vector of two qubits whose entries are Gaussian
integers over `2^k` is prepared, controlled on the data qubit, by an `{H, T, CNOT}` circuit on the
three wires (data + two ancillas, no further ancilla) with `O(k)` gates; the constant `A` is
absolute. -/
theorem controlled_preparation :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (v : EuclideanSpace ℂ (Qubits 2)), IsState v →
      (∀ z, ∃ a b : ℤ, v z = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 : ℂ) ^ k) →
      ∃ c : Circuit htcxGateSet (1 + 2), PreparesControlled c.unitary v ∧
        (c.size : ℝ) ≤ A * ((k : ℝ) + 1) := by sorry

end CliffordTApprox.Ancilla
