-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_10
-- name    : AutoQMem.Lindblad.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:08.785542+00:00
-- url     : https://prove2.me/theorems/4366db7d-466d-4e0c-9845-6acaf110aed8
-- title:
--   Lemma 4.10: $\Lambda_X(e)=(-1)^{b_X(e)}$ and $\Lambda_Z(e)=(-1)^{b_Z(e)}$
-- statement:
--   Let $\Lambda_X=\Phi_X(T_X)$ and $\Lambda_Z=\Phi_Z(T_Z)$ be the logical-error phases and $b_X,b_Z$ the decoded logical values. For every error vector $e\in\mathbb F_2^n$,
--   $$\Lambda_X(e)=(-1)^{b_X(e)},\qquad \Lambda_Z(e)=(-1)^{b_Z(e)} .$$
--
--   The classical image of the decoded logical observable is exactly the sign of the classical logical readout.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
--   - encoding: Λ_X ∈ ℝ^{Ω_X} → Λ_X complex valued; reason: Φ_X is formalized with complex values; the identity shows Λ_X takes the values ±1
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.10, eq. (96), p. 36 (PDF p. 38)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_PhiX__43fab1
import Definitions.Def_AutoQMem_Lindblad_decodedValue
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.10 (Binary and phase descriptions of the decoded logical error).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.10,
eq. (96), p. 36 (PDF 38).

For every error vector `e`, `Λ_X(e) = (−1)^{b_X(e)}` and `Λ_Z(e) = (−1)^{b_Z(e)}`, where
`b_X(e) = ℓ_X · (e ⊕ Dec_X(H_X e))` is the decoded logical value. -/
theorem lemma_4_10 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ) :
    (∀ e : Fin (n' + 1) → ZMod 2,
      Q.LambdaX DX e = (-1 : ℂ) ^ (decodedValue C.HX Q.lX DX e).val) ∧
    (∀ e : Fin (n' + 1) → ZMod 2,
      Q.LambdaZ DZ e = (-1 : ℂ) ^ (decodedValue C.HZ Q.lZ DZ e).val) := by sorry

end AutoQMem.Lindblad
