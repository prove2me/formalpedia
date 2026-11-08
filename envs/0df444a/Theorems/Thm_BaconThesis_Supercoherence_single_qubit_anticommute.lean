-- Prove2me | Theorems.Thm_BaconThesis_Supercoherence_single_qubit_anticommute
-- name    : BaconThesis.Supercoherence.single_qubit_anticommute
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:17:45.864393+00:00
-- url     : https://prove2.me/theorems/65a514e8-a4a5-4ad0-a3a4-c8b0c0668cdb
-- title:
--   Every single-qubit Pauli $\sigma_\alpha^{(i)}$ anticommutes with $S_1$ or $S_2$
-- statement:
--   The $[4,2,2]$ code detects every single-qubit error: for every qubit $i \in \{1,2,3,4\}$ and every $\alpha \in \{x, y, z\}$, the operator $\sigma_\alpha^{(i)}$ ($\sigma_\alpha$ on qubit $i$, identity elsewhere) anticommutes with at least one of the stabilizer generators,
--
--   $$\sigma_\alpha^{(i)} S_1 = -S_1 \sigma_\alpha^{(i)} \quad\text{or}\quad \sigma_\alpha^{(i)} S_2 = -S_2 \sigma_\alpha^{(i)} .$$
--
--   Differences from the source:
--   - encoding: σ_α^{(i)}, α ∈ {x, y, z}, i ∈ {1,…,4} → `pauliAt a i` with a ∈ {1, 2, 3} (a ≠ 0) and i ∈ Fin 4; reason: the referenced Pauli indexing (0 = I, 1 = σ_x, 2 = σ_y, 3 = σ_z) and 0-based qubits
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186): "Thus every single qubit operator σ_α^{(i)} anticommutes with at
least one of S1 and S2." For every qubit `i` of the four and every Pauli matrix `σ_α`,
`α ∈ {x, y, z}`, the operator `σ_α^{(i)}` (σ_α on qubit `i`, identity elsewhere) anticommutes with
`S₁` or with `S₂`.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; Pauli strings via `QMaxCutSDP.Rounding.pauliString` (`pauli 0,1,2,3 = I, σ_x, σ_y, σ_z`); the book's qubit `k` is Lean's qubit `k - 1`. `σ_α^{(i)}` is `pauliAt a i` with `a ∈ {1, 2, 3}` (`a ≠ 0`); anticommuting is
`A B = −(B A)`. -/
theorem single_qubit_anticommute (i : Fin 4) (a : Fin 4) (ha : a ≠ 0) :
    pauliAt a i * S1 = -(S1 * pauliAt a i) ∨ pauliAt a i * S2 = -(S2 * pauliAt a i) := by sorry

end BaconThesis.Supercoherence
