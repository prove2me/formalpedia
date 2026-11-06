-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_corollary_4_5
-- name    : AutoQMem.Lindblad.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:42.472616+00:00
-- url     : https://prove2.me/theorems/d6ebcb11-2389-46cd-b586-e6ab3ba00386
-- title:
--   Corollary 4.5: $\mathcal L^*(t)(O_X)=\sum_i\Gamma^{(X)}_i(t)(Z_iO_XZ_i-O_X)$ on $V_X$
-- statement:
--   Let $\mathcal L(t)$ be a syndrome-based Lindbladian and $t\ge0$. For every $O_X\in V_X$,
--   $$\mathcal L^*(t)(O_X)=\sum_{i=1}^n\Gamma^{(X)}_i(t)\bigl(Z_iO_XZ_i-O_X\bigr),$$
--   and for every $O_Z\in V_Z$,
--   $$\mathcal L^*(t)(O_Z)=\sum_{i=1}^n\Gamma^{(Z)}_i(t)\bigl(X_iO_ZX_i-O_Z\bigr).$$
--
--   On the sector subspaces the Heisenberg generator depends only on the total flip-rate operators.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open → the Lindbladian structure carries the R1 regularity fields (measurable on [0,∞), bounded on every [0,T]); reason: the paper's Remark 2.26 regularity, needed for the propagators used elsewhere in the mission; the statement itself uses the Lindbladian only at the fixed times t ≥ 0
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
--   - encoding: L*(t) for the syndrome-based Lindbladian L(t) → t ≥ 0 is a hypothesis; reason: Definition 2.22 imposes its membership conditions for t ≥ 0
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Corollary 4.5, eqs. (86)–(87), p. 34 (PDF p. 36)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_gen
open Matrix

namespace AutoQMem.Lindblad

/-- **Corollary 4.5 (Sector-restricted instantaneous dynamics).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Corollary 4.5,
eqs. (86)–(87), p. 34 (PDF 36).

Let `L(t)` be a syndrome-based Lindbladian, `t ≥ 0` and `O_X ∈ V_X`. Then
`L*(t)(O_X) = Σ_i Γ^{(X)}_i(t) (Z_i O_X Z_i − O_X)`; similarly, for `O_Z ∈ V_Z`,
`L*(t)(O_Z) = Σ_i Γ^{(Z)}_i(t) (X_i O_Z X_i − O_Z)`.

**Formalization Note.** `t ≥ 0` is where Definition 2.22's membership conditions hold. -/
theorem corollary_4_5 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) {ι : Type} [Fintype ι] (L : SyndromeLindbladian C ι)
    (t : ℝ) (ht : 0 ≤ t) :
    (∀ O : Op (n' + 1), Q.inVX O →
      L.genAdj t O = ∑ i, flipRateX (L.jump t) i * (pauliAt .Z i * O * pauliAt .Z i - O)) ∧
    (∀ O : Op (n' + 1), Q.inVZ O →
      L.genAdj t O = ∑ i, flipRateZ (L.jump t) i * (pauliAt .X i * O * pauliAt .X i - O)) := by sorry

end AutoQMem.Lindblad
