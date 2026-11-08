-- Prove2me | Theorems.Thm_BaconThesis_Supercoherence_eq_15_8
-- name    : BaconThesis.Supercoherence.eq_15_8
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:18:12.840402+00:00
-- url     : https://prove2.me/theorems/560f448c-c2f2-4921-a9de-35d9f586a116
-- title:
--   Eq. (15.8) — $H=\bar X_1(I+S_1)+\bar Z_1(I+S_2)$
-- statement:
--   The Hamiltonian (15.7) written in terms of the $[4,2,2]$ code: with the stabilizer generators $S_1, S_2$ of (15.5) and the logical operators $\bar X_1 = \sigma_x\otimes\sigma_x\otimes I\otimes I$, $\bar Z_1 = I\otimes\sigma_z\otimes\sigma_z\otimes I$ of (15.6),
--
--   $$H = \bar X_1 + \bar X_1 S_1 + \bar Z_1 + \bar Z_1 S_2 = \bar X_1 (I + S_1) + \bar Z_1 (I + S_2).$$
--
--   Differences from the source:
--   - encoding: qubits 1–4 → Lean qubits 0–3 (Pauli strings over `Fin 4`); reason: index base only
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.8), p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_X1bar
import Definitions.Def_BaconThesis_Supercoherence_Z1bar
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.8), p.169 (PDF p.186): the Hamiltonian (15.7) written in terms of the [4,2,2]
code, `H = X̄₁ + X̄₁S₁ + Z̄₁ + Z̄₁S₂ = X̄₁(I + S₁) + Z̄₁(I + S₂)`.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; Pauli strings via `QMaxCutSDP.Rounding.pauliString` (`pauli 0,1,2,3 = I, σ_x, σ_y, σ_z`); the book's qubit `k` is Lean's qubit `k - 1`. -/
theorem eq_15_8 :
    codeHamiltonian = X1bar + X1bar * S1 + Z1bar + Z1bar * S2 ∧
      codeHamiltonian = X1bar * (1 + S1) + Z1bar * (1 + S2) := by sorry

end BaconThesis.Supercoherence
