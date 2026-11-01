-- Prove2me | Theorems.Thm_BaconThesis_Supercoherence_sector_eigenvalues
-- name    : BaconThesis.Supercoherence.sector_eigenvalues
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:29.177728+00:00
-- url     : https://prove2.me/theorems/952b24bd-792d-428c-87af-2989f9b3bdb2
-- title:
--   The eigenvalues of $H$ on the four sectors are $\pm2\sqrt2$, $\pm2$, $\pm2$ and $0$
-- statement:
--   The eigenvalues of the Hamiltonian (15.7) on the joint eigenspaces of the stabilizer generators are exactly
--
--   $$\operatorname{spec}_{+,+}(H) = \{2\sqrt2, -2\sqrt2\},\quad \operatorname{spec}_{+,-}(H) = \{2,-2\},\quad \operatorname{spec}_{-,+}(H) = \{2,-2\},\quad \operatorname{spec}_{-,-}(H) = \{0\},$$
--
--   where $\operatorname{spec}_{s_1,s_2}(H)$ is the set of eigenvalues of $H$ having an eigenvector $v$ with $S_1 v = s_1 v$ and $S_2 v = s_2 v$. Each listed value occurs and no other value does.
--
--   Differences from the source:
--   - encoding: "the eigenvalues of H for these four cases" → the set of μ with an eigenvector of H in the (s₁, s₂) joint eigenspace, as an equality of sets; reason: H commutes with S₁, S₂, so this is the spectrum of H restricted to the sector
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, sentence after eq. (15.9), p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_sectorSpectrum

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, sentence after eq. (15.9), p.169 (PDF p.186): "The eigenvalues of H for these four cases
are thus ±2√2, ±2, ±2, and 0 respectively." The eigenvalues of the Hamiltonian (15.7) on the joint
eigenspaces `(S₁, S₂) = (+1, +1), (+1, −1), (−1, +1), (−1, −1)` are exactly `{2√2, −2√2}`,
`{2, −2}`, `{2, −2}` and `{0}`.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; Pauli strings via `QMaxCutSDP.Rounding.pauliString` (`pauli 0,1,2,3 = I, σ_x, σ_y, σ_z`); the book's qubit `k` is Lean's qubit `k - 1`. `sectorSpectrum s₁ s₂` is the set of eigenvalues of `H` with an eigenvector in the
`(s₁, s₂)` joint eigenspace; each conjunct is an equality of sets, so both every listed value
occurs and no other value occurs. -/
theorem sector_eigenvalues :
    sectorSpectrum 1 1 = {((2 * Real.sqrt 2 : ℝ) : ℂ), ((-(2 * Real.sqrt 2) : ℝ) : ℂ)} ∧
      sectorSpectrum 1 (-1) = {2, -2} ∧ sectorSpectrum (-1) 1 = {2, -2} ∧
      sectorSpectrum (-1) (-1) = {0} := by sorry

end BaconThesis.Supercoherence
