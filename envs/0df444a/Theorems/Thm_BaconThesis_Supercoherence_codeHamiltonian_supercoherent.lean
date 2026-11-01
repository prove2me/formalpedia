-- Prove2me | Theorems.Thm_BaconThesis_Supercoherence_codeHamiltonian_supercoherent
-- name    : BaconThesis.Supercoherence.codeHamiltonian_supercoherent
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:32.699918+00:00
-- url     : https://prove2.me/theorems/502fbbd8-6152-4360-99a1-86e5d1b7394f
-- title:
--   The $[4,2,2]$-code Hamiltonian (15.7) is supercoherent, with a two-fold degenerate ground space at energy $-2\sqrt2$
-- statement:
--   Let $H = \sigma_x\otimes\sigma_x\otimes I\otimes I + I\otimes I\otimes\sigma_x\otimes\sigma_x + I\otimes\sigma_z\otimes\sigma_z\otimes I + \sigma_z\otimes I\otimes I\otimes\sigma_z$ be the four-qubit Hamiltonian (15.7). Then
--
--   1. the lowest eigenvalue of $H$ is $-2\sqrt2$;
--   2. the ground space $\mathcal G = \{v : Hv = -2\sqrt2\,v\}$ is two-dimensional (the ground state is two-fold degenerate, "corresponding directly to the second encoded qubit");
--   3. $H$ is supercoherent in the sense of Definition 15.2.1: for every qubit $k$, every traceless single-qubit operator $O$ and all $|i\rangle, |j\rangle \in \mathcal G$,
--
--   $$\langle j|\,O^{(k)}\,|i\rangle = 0 ,$$
--
--   that is, every single-qubit operator takes the system out of the degenerate ground space into higher-energy states.
--
--   This is the chapter's example of a supercoherent qubit: the second encoded qubit of the $[4,2,2]$ code, stored in the ground space of $H$, can be disturbed by a single-qubit error only by raising its energy.
--
--   Differences from the source:
--   - reading: "every single qubit operator" in Definition 15.2.1 and (15.10) → every traceless single-qubit operator on any qubit; reason: over all operators (15.10) with o = I would require ⟨i|i⟩ = 0 for every ground state, so no Hamiltonian would be supercoherent; the section's single-qubit errors σ_α^{(i)} span exactly the traceless operators, and the traceless reading is the strongest satisfiable one
--   - reading: "takes the system out of states in this degenerate ground state" → maps every ground state into the orthogonal complement of the ground space, as in (15.10); reason: (15.10) is the definition's stated criterion
--   - encoding: "the ground state" → the eigenspace of the lowest eigenvalue, with the lowest eigenvalue given by `IsGroundEnergy` (an eigenvalue, below the real part of every eigenvalue); reason: H is Hermitian, so its eigenvalues are real
--   - encoding: "a system Hamiltonian H which has a degenerate ground state" → `IsSupercoherent` requires `H.IsHermitian` and `2 ≤ finrank` of the ground space; reason: a Hamiltonian is a Hermitian operator, and a degenerate ground state is a ground space of dimension at least 2
--   - encoding: qubits 1–4 → Lean qubits 0–3; reason: index base only
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eqs. (15.7)–(15.9), p.169 (PDF p.186), and Definition 15.2.1 with eq. (15.10), pp.170–171 (PDF pp.187–188)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian
import Definitions.Def_BaconThesis_Supercoherence_groundSpace
import Definitions.Def_BaconThesis_Supercoherence_IsGroundEnergy
import Definitions.Def_BaconThesis_Supercoherence_IsSupercoherent

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §15.2, eqs. (15.7)–(15.9) with Definition 15.2.1 and (15.10), pp.169–171
(PDF pp.186–188): "Here we see that the ground state of the code is actually two-fold degenerate:
corresponding directly to the second encoded qubit." … "Every single qubit operator changes a value
of S1 and S2 and therefore takes the system from the ground state to a higher energy state. We term
such a Hamiltonian a supercoherent Hamiltonian". For the Hamiltonian
`H = σ_x⊗σ_x⊗I⊗I + I⊗I⊗σ_x⊗σ_x + I⊗σ_z⊗σ_z⊗I + σ_z⊗I⊗I⊗σ_z` of (15.7):
1. the lowest eigenvalue of `H` is `−2√2`;
2. the ground space of `H` has dimension exactly 2;
3. `H` is supercoherent (Definition 15.2.1): every traceless single-qubit operator on any of the
   four qubits maps the ground space into its orthogonal complement.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; Pauli strings via `QMaxCutSDP.Rounding.pauliString` (`pauli 0,1,2,3 = I, σ_x, σ_y, σ_z`); the book's qubit `k` is Lean's qubit `k - 1`. "Every single qubit operator" is read as every traceless single-qubit operator, see
`IsSupercoherent`. -/
theorem codeHamiltonian_supercoherent :
    IsGroundEnergy codeHamiltonian (-(2 * Real.sqrt 2)) ∧
      Module.finrank ℂ (groundSpace codeHamiltonian (-(2 * Real.sqrt 2))) = 2 ∧
      IsSupercoherent codeHamiltonian := by sorry

end BaconThesis.Supercoherence
