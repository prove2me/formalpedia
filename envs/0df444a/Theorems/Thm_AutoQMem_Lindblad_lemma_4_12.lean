-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_12
-- name    : AutoQMem.Lindblad.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:11.056505+00:00
-- url     : https://prove2.me/theorems/20823228-8ec1-4833-bbac-8e8e74357a90
-- title:
--   Lemma 4.12: $\Phi_X(Z_iOZ_i)(e)=\Phi_X(O)(e\oplus\hat e_i)$
-- statement:
--   Let $O=\bar XA\in V_X$. Then $Z_iOZ_i\in V_X$ and for every $e\in\mathbb F_2^n$
--   $$\Phi_X(Z_iOZ_i)(e)=\Phi_X(O)(e\oplus\hat e_i).$$
--   Similarly, for $O=\bar ZB\in V_Z$, $X_iOX_i\in V_Z$ and $\Phi_Z(X_iOX_i)(e)=\Phi_Z(O)(e\oplus\hat e_i)$.
--
--   Conjugation by a physical Pauli becomes a single hop in the classical error-configuration space.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
--   - generalization: Φ_X : V_X → ℝ^{Ω_X} → Φ_X(O)(e) = (−1)^{ℓ_X·e}(X̄O)(H_X e), complex valued, for O = X̄A with any A in the complex algebra A_X; reason: A_X is a complex algebra and Φ_X is extended linearly; for Hermitian A the values are real and the statement specializes to the paper's
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.12, eq. (104), p. 36 (PDF p. 38); proof Appendix B, p. 65 (PDF p. 67)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_PhiX__43fab1
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_pauliAt
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.12 (Pauli conjugation as error vector shift).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.12, eq. (104),
p. 36 (PDF 38); proof Appendix B, p. 65 (PDF 67).

Let `O = X̄A ∈ V_X`. Then `Z_i O Z_i ∈ V_X` and `Φ_X(Z_i O Z_i)(e) = Φ_X(O)(e ⊕ ê_i)`.
Similarly, for `O = Z̄B ∈ V_Z`, `X_i O X_i ∈ V_Z` and `Φ_Z(X_i O X_i)(e) = Φ_Z(O)(e ⊕ ê_i)`. -/
theorem lemma_4_12 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (i : Fin (n' + 1)) :
    (∀ O : Op (n' + 1), Q.inVX O →
      Q.inVX (pauliAt .Z i * O * pauliAt .Z i) ∧
        ∀ e, Q.PhiX (pauliAt .Z i * O * pauliAt .Z i) e = Q.PhiX O (e + Pi.single i 1)) ∧
    (∀ O : Op (n' + 1), Q.inVZ O →
      Q.inVZ (pauliAt .X i * O * pauliAt .X i) ∧
        ∀ e, Q.PhiZ (pauliAt .X i * O * pauliAt .X i) e = Q.PhiZ O (e + Pi.single i 1)) := by sorry

end AutoQMem.Lindblad
