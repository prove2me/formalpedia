-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_14
-- name    : AutoQMem.Lindblad.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:25.440277+00:00
-- url     : https://prove2.me/theorems/d5e50c04-b659-4b91-87ff-81fb8abd6c46
-- title:
--   Lemma 4.14: $\langle T_X,O\rangle_{\mathrm{code}}=\Phi_X(O)(0)$ on $V_X$
-- statement:
--   Let $O=\bar XF\in V_X$. Then
--   $$\langle T_X,O\rangle_{\mathrm{code}}=\Phi_X(O)(0).$$
--   Similarly, for $O=\bar ZF\in V_Z$, $\langle T_Z,O\rangle_{\mathrm{code}}=\Phi_Z(O)(0)$.
--
--   The code-space inner product with the decoded logical observable is evaluation of the classical representative at the vacuum error vector.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
--   - generalization: Φ_X : V_X → ℝ^{Ω_X} → Φ_X(O)(e) = (−1)^{ℓ_X·e}(X̄O)(H_X e), complex valued, for O = X̄A with any A in the complex algebra A_X; reason: A_X is a complex algebra and Φ_X is extended linearly; for Hermitian A the values are real and the statement specializes to the paper's
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.14, eqs. (107)–(108), p. 38 (PDF p. 40); proof Appendix B, p. 67 (PDF p. 69)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_PhiX__43fab1
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_codeInner
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.14 (Classical representation of code space inner product).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.14,
eqs. (107)–(108), p. 38 (PDF 40); proof Appendix B, p. 67 (PDF 69).

Let `O = X̄F ∈ V_X`. Then `⟨T_X, O⟩_code = Φ_X(O)(0)`. Similarly, for `O = Z̄F ∈ V_Z`,
`⟨T_Z, O⟩_code = Φ_Z(O)(0)`. -/
theorem lemma_4_14 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ) :
    (∀ O : Op (n' + 1), Q.inVX O → Q.codeInner (Q.TX DX) O = Q.PhiX O 0) ∧
    (∀ O : Op (n' + 1), Q.inVZ O → Q.codeInner (Q.TZ DZ) O = Q.PhiZ O 0) := by sorry

end AutoQMem.Lindblad
