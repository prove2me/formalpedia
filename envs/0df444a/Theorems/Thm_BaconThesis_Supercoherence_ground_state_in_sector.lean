-- Prove2me | Theorems.Thm_BaconThesis_Supercoherence_ground_state_in_sector
-- name    : BaconThesis.Supercoherence.ground_state_in_sector
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:38.4721+00:00
-- url     : https://prove2.me/theorems/91a05444-814b-4aef-b46d-5415c8cd4cdd
-- title:
--   The ground states of $H$ have energy $-2\sqrt2$ and lie in the sector $S_1=S_2=+1$
-- statement:
--   The lowest eigenvalue of the Hamiltonian (15.7) is $-2\sqrt2$, and every ground state $v$ (every $v$ with $Hv = -2\sqrt2\, v$) lies in the $S_1 = +1$, $S_2 = +1$ subspace of the $[4,2,2]$ code and is a $-\sqrt2$ eigenvector of the first-encoded-qubit operator $\bar X_1 + \bar Z_1$:
--
--   $$S_1 v = v,\qquad S_2 v = v,\qquad (\bar X_1 + \bar Z_1) v = -\sqrt2\, v .$$
--
--   By (15.9) the last identity is the statement that $v$ realizes "the $-2\sqrt2$ eigenvalue of $H$ over the first encoded qubit".
--
--   Differences from the source:
--   - reading: "will be the −2√2 eigenvalue of H over the first encoded qubit" → the lowest eigenvalue of H is −2√2 and every ground state is a −√2 eigenvector of X̄₁ + Z̄₁; reason: on the S₁ = S₂ = +1 sector H = 2(X̄₁ + Z̄₁) by (15.9), and X̄₁ + Z̄₁ is the first encoded qubit's part of H
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_X1bar
import Definitions.Def_BaconThesis_Supercoherence_Z1bar
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian
import Definitions.Def_BaconThesis_Supercoherence_groundSpace
import Definitions.Def_BaconThesis_Supercoherence_IsGroundEnergy

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186): "We therefore see that the ground state of H will be within the
S1 = +1, S2 = +1 subspace of the [4, 2, 2] code and will be the −2√2 eigenvalue of H over the first
encoded qubit." The lowest eigenvalue of the Hamiltonian (15.7) is `−2√2`, and every vector `v` of
its ground space satisfies `S₁ v = v`, `S₂ v = v` and `(X̄₁ + Z̄₁) v = −√2 v` (so that
`H v = 2(X̄₁ + Z̄₁) v = −2√2 v` by (15.9)).

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; Pauli strings via `QMaxCutSDP.Rounding.pauliString` (`pauli 0,1,2,3 = I, σ_x, σ_y, σ_z`); the book's qubit `k` is Lean's qubit `k - 1`. "The −2√2 eigenvalue of H over the first encoded qubit" is rendered as the eigenvalue
equation of the first-qubit operator `X̄₁ + Z̄₁`, whose doubling is `H` on the `(+1, +1)`
sector. -/
theorem ground_state_in_sector :
    IsGroundEnergy codeHamiltonian (-(2 * Real.sqrt 2)) ∧
      ∀ v ∈ groundSpace codeHamiltonian (-(2 * Real.sqrt 2)),
        S1 *ᵥ v = v ∧ S2 *ᵥ v = v ∧ (X1bar + Z1bar) *ᵥ v = (-(Real.sqrt 2 : ℂ)) • v := by sorry

end BaconThesis.Supercoherence
