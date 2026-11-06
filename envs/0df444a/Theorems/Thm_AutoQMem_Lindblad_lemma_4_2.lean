-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_2
-- name    : AutoQMem.Lindblad.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:00.486174+00:00
-- url     : https://prove2.me/theorems/93166d09-b6af-46b1-ab2f-157e7d2e3958
-- title:
--   Lemma 4.2: $T_X=\bar X\varphi_X$ and $T_Z=\bar Z\varphi_Z$
-- statement:
--   Let $T_X,T_Z$ be the decoded logical observables of a designated logical qubit of a CSS code, and $\varphi_X,\varphi_Z$ the readout decoder phase operators of Definition 4.1. Then
--   $$T_X=\bar X\varphi_X,\qquad T_Z=\bar Z\varphi_Z,$$
--   and $\varphi_X\in\mathcal A_X$, $\varphi_Z\in\mathcal A_Z$.
--
--   This places the decoded logical observables in the logical sector subspaces $V_X$, $V_Z$.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.2, eq. (82), p. 33 (PDF p. 35); proof Appendix B, p. 64 (PDF p. 66)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_TX
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_phiX
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.2 (Algebraic reduction of decoded logical observables).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.2,
eq. (82), p. 33 (PDF 35); proof Appendix B, p. 64 (PDF 66).

`T_X = X̄ φ_X` and `T_Z = Z̄ φ_Z`, where `φ_X ∈ A_X` and `φ_Z ∈ A_Z` are the diagonal syndrome
operators of Definition 4.1. -/
theorem lemma_4_2 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ) :
    (Q.TX DX = pauliX Q.lX * Q.phiX DX ∧ Q.phiX DX ∈ C.algX) ∧
    (Q.TZ DZ = pauliZ Q.lZ * Q.phiZ DZ ∧ Q.phiZ DZ ∈ C.algZ) := by sorry

end AutoQMem.Lindblad
