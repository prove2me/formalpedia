-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_proposition_4_6
-- name    : AutoQMem.Lindblad.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:17.67047+00:00
-- url     : https://prove2.me/theorems/ab943d6d-f811-4f5b-89e4-11d1acc0abc8
-- title:
--   Proposition 4.6: $\mathcal L^*(t)(V_X)\subseteq V_X$ and $\mathcal L^*(t)(V_Z)\subseteq V_Z$
-- statement:
--   Let $\mathcal L(t)$ be a syndrome-based Lindbladian. Then for every $t\ge0$,
--   $$\mathcal L^*(t)(V_X)\subseteq V_X,\qquad \mathcal L^*(t)(V_Z)\subseteq V_Z .$$
--
--   The logical sector subspaces are closed under the instantaneous Heisenberg generator; this is where the rate condition (33) enters.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open → the Lindbladian structure carries the R1 regularity fields (measurable on [0,∞), bounded on every [0,T]); reason: the paper's Remark 2.26 regularity, needed for the propagators used elsewhere in the mission; the statement itself uses the Lindbladian only at the fixed times t ≥ 0
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Proposition 4.6, eq. (88), p. 34 (PDF p. 36)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_gen
open Matrix

namespace AutoQMem.Lindblad

/-- **Proposition 4.6 (Syndrome-based Lindbladians preserve the logical sector subspaces).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Proposition 4.6, eq. (88), p. 34 (PDF 36).

For every `t ≥ 0`, `L*(t)(V_X) ⊆ V_X` and `L*(t)(V_Z) ⊆ V_Z`. -/
theorem proposition_4_6 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) {ι : Type} [Fintype ι] (L : SyndromeLindbladian C ι) :
    ∀ t : ℝ, 0 ≤ t →
      (∀ O : Op (n' + 1), Q.inVX O → Q.inVX (L.genAdj t O)) ∧
      (∀ O : Op (n' + 1), Q.inVZ O → Q.inVZ (L.genAdj t O)) := by sorry

end AutoQMem.Lindblad
