-- Prove2me | Theorems.Thm_CollectiveDFS_exchange_pauli
-- name    : CollectiveDFS.exchange_pauli
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:17.718751+00:00
-- url     : https://prove2.me/theorems/c07f33fb-830f-422f-9446-67918380c16d
-- title:
--   (7.22), p.26 — exchange in Pauli form
-- statement:
--   For distinct qubits $a\neq b$ of an $n$-qubit register,
--   $$E_{ab}=\tfrac12\big(I+\sigma^a_x\sigma^b_x+\sigma^a_y\sigma^b_y+\sigma^a_z\sigma^b_z\big).$$
--
--   Together with (A1) it expresses every partial Casimir through exchanges, (7.23).
--
--   Differences from the source:
--   - encoding: qubits 1, …, n; |0⟩, |1⟩ → 0-based wires Fin n; Bool basis with false = |0⟩; reason: Lean convention; same operators
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.22), p.26

import Mathlib
import Definitions.Def_CollectiveDFS_exchange
import Definitions.Def_CollectiveDFS_pauli
import Definitions.Def_CollectiveDFS_onWire

open QAlgorithms

namespace CollectiveDFS

/-- Eq. (7.22) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D, p.26, PDF p.26): for wires `a ≠ b`,
`E_ab = ½ (I + σ_x^a σ_x^b + σ_y^a σ_y^b + σ_z^a σ_z^b)`.

**Formalization Note** `exchange a b` is defined as the permutation matrix of the two wires; this
theorem ties it to the Pauli form. `pauli 0, 1, 2 = σ_x, σ_y, σ_z` of (5.2); `onWire a σ` is
`σ^a`; wires 0-based. -/
theorem exchange_pauli (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    exchange a b =
      (1 / 2 : ℂ) • (1 + ∑ α : Fin 3, onWire a (pauli α) * onWire b (pauli α)) := by sorry

end CollectiveDFS
