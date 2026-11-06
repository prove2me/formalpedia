-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_4
-- name    : AutoQMem.Lindblad.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:51.668957+00:00
-- url     : https://prove2.me/theorems/26a8662f-f908-44c0-af0a-040d9b2ee49f
-- title:
--   Lemma 4.4: a single jump acts on $V_X$ by $\mathbf 1_{P\in\{Z,Y\}}f^\dagger f(Z_iOZ_i-O)$
-- statement:
--   Let $i$ be a qubit, $P\in\{I,X,Y,Z\}$ and $f\in\mathcal A$. For every $O\in V_X$,
--   $$\mathcal D[P_if]^*(O)=\mathbf 1_{P\in\{Z,Y\}}\,f^\dagger f\,(Z_iOZ_i-O),$$
--   and for every $O_Z\in V_Z$,
--   $$\mathcal D[P_if]^*(O_Z)=\mathbf 1_{P\in\{X,Y\}}\,f^\dagger f\,(X_iO_ZX_i-O_Z).$$
--
--   A jump acts on a sector subspace only through conjugation by its Pauli factor, weighted by its rate operator $f^\dagger f$.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: the printed (84) writes both O and O_X for the element of V_X → one operator O ∈ V_X; reason: both symbols denote the same operator
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.4, eqs. (84)–(85), p. 34 (PDF p. 36); proof Appendix B, p. 65 (PDF p. 67)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_diss
import Definitions.Def_AutoQMem_Lindblad_pauliAt
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.4 (Action of a single jump on the sector subspaces).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.4,
eqs. (84)–(85), p. 34 (PDF 36); proof Appendix B, p. 65 (PDF 67).

Let `i` be a qubit, `P ∈ {I, X, Y, Z}` and `f ∈ A`. For every `O ∈ V_X`,
`D[P_i f]*(O) = 1_{P∈{Z,Y}} f†f (Z_i O Z_i − O)`, and for every `O_Z ∈ V_Z`,
`D[P_i f]*(O_Z) = 1_{P∈{X,Y}} f†f (X_i O_Z X_i − O_Z)`.

**Formalization Note.** The printed (84) writes both `O` and `O_X` for the same element of
`V_X`. -/
theorem lemma_4_4 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (i : Fin (n' + 1)) (P : Pauli1) (f : Op (n' + 1))
    (hf : f ∈ C.alg) :
    (∀ O : Op (n' + 1), Q.inVX O → dissAdj (pauliAt P i * f) O =
      if P = .Z ∨ P = .Y then fᴴ * f * (pauliAt .Z i * O * pauliAt .Z i - O) else 0) ∧
    (∀ O : Op (n' + 1), Q.inVZ O → dissAdj (pauliAt P i * f) O =
      if P = .X ∨ P = .Y then fᴴ * f * (pauliAt .X i * O * pauliAt .X i - O) else 0) := by sorry

end AutoQMem.Lindblad
