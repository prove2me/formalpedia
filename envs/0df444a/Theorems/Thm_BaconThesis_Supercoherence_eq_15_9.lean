-- Prove2me | Theorems.Thm_BaconThesis_Supercoherence_eq_15_9
-- name    : BaconThesis.Supercoherence.eq_15_9
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:18:13.967761+00:00
-- url     : https://prove2.me/theorems/8fc608e2-5b19-4acf-81d2-d65685b48eaa
-- title:
--   Eq. (15.9) — the action of $H$ on each stabilizer sector
-- statement:
--   On the joint eigenspaces of the stabilizer generators the Hamiltonian (15.7) acts as follows: for every vector $v$ of $(\mathbb C^2)^{\otimes 4}$,
--
--   $$\begin{aligned} S_1 v = v,\ S_2 v = v &\Rightarrow H v = 2(\bar X_1 + \bar Z_1) v,\\ S_1 v = v,\ S_2 v = -v &\Rightarrow H v = 2\bar X_1 v,\\ S_1 v = -v,\ S_2 v = v &\Rightarrow H v = 2\bar Z_1 v,\\ S_1 v = -v,\ S_2 v = -v &\Rightarrow H v = 0. \end{aligned}$$
--
--   Differences from the source:
--   - encoding: "S1 = ±1, S2 = ±1 ⇒ H = …" → for every vector v in the joint eigenspace, H v equals the stated operator applied to v; reason: this is what an operator identity on a subspace means
--   - encoding: qubits 1–4 → Lean qubits 0–3; reason: index base only
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.9), p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_X1bar
import Definitions.Def_BaconThesis_Supercoherence_Z1bar
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.9), p.169 (PDF p.186): on the joint eigenspace of the stabilizer generators with
eigenvalues `(S₁, S₂) = (+1, +1), (+1, −1), (−1, +1), (−1, −1)` the Hamiltonian (15.7) acts as
`2(X̄₁ + Z̄₁)`, `2X̄₁`, `2Z̄₁` and `0` respectively: for every vector `v` in that joint eigenspace,
`H v` equals the stated operator applied to `v`.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; Pauli strings via `QMaxCutSDP.Rounding.pauliString` (`pauli 0,1,2,3 = I, σ_x, σ_y, σ_z`); the book's qubit `k` is Lean's qubit `k - 1`. -/
theorem eq_15_9 (v : (Fin 4 → Fin 2) → ℂ) :
    (S1 *ᵥ v = v → S2 *ᵥ v = v → codeHamiltonian *ᵥ v = ((2 : ℂ) • (X1bar + Z1bar)) *ᵥ v) ∧
      (S1 *ᵥ v = v → S2 *ᵥ v = -v → codeHamiltonian *ᵥ v = ((2 : ℂ) • X1bar) *ᵥ v) ∧
      (S1 *ᵥ v = -v → S2 *ᵥ v = v → codeHamiltonian *ᵥ v = ((2 : ℂ) • Z1bar) *ᵥ v) ∧
      (S1 *ᵥ v = -v → S2 *ᵥ v = -v → codeHamiltonian *ᵥ v = 0) := by sorry

end BaconThesis.Supercoherence
