-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_B_1
-- name    : AutoQMem.Lindblad.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:24.035536+00:00
-- url     : https://prove2.me/theorems/a066ef7d-6603-4c1a-a4f9-336c92884e47
-- title:
--   Lemma B.1: the stabilizer algebra commutes with $V_X\cup V_Z$
-- statement:
--   Let $\mathcal A$ be the full stabilizer algebra of a CSS code with a designated logical qubit. Every $F\in\mathcal A$ commutes with every $T\in V_X\cup V_Z$:
--   $$[F,T]=0 .$$
--   In particular, for a syndrome-based Lindbladian and every $t\ge0$, the Hamiltonian term vanishes on the sector subspaces: $i[H(t),T]=0$ for $T\in V_X\cup V_Z$.
--
--   This is the first step in showing that the Heisenberg dynamics preserves the sector subspaces.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: the Hamiltonian term of a syndrome-based Lindbladian → the term i[H(t), T] at times t ≥ 0; reason: Definition 2.22 places H(t) in A for t ≥ 0
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open → the Lindbladian structure carries the R1 regularity fields (measurable on [0,∞), bounded on every [0,T]); reason: the paper's Remark 2.26 regularity, needed for the propagators used elsewhere in the mission; the statement itself uses the Lindbladian only at the fixed times t ≥ 0
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma B.1, p. 65 (PDF p. 67)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma B.1 (The stabilizer algebra commutes with the sector subspaces).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma B.1,
p. 65 (PDF 67).

Every `F ∈ A` satisfies `[F, T] = 0` for all `T ∈ V_X ∪ V_Z`. In particular, the Hamiltonian term
`i[H(t), T]` of a syndrome-based Lindbladian vanishes on `V_X` and `V_Z` (for `t ≥ 0`, where
`H(t) ∈ A`). -/
theorem lemma_B_1 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) :
    (∀ F ∈ C.alg, ∀ T : Op (n' + 1), (Q.inVX T ∨ Q.inVZ T) → F * T = T * F) ∧
    (∀ (ι : Type) [Fintype ι] (L : SyndromeLindbladian C ι) (t : ℝ), 0 ≤ t →
      ∀ T : Op (n' + 1), (Q.inVX T ∨ Q.inVZ T) →
        Complex.I • (L.ham t * T - T * L.ham t) = 0) := by sorry

end AutoQMem.Lindblad
