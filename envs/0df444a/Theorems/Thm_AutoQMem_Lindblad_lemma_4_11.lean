-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_11
-- name    : AutoQMem.Lindblad.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:40.564095+00:00
-- url     : https://prove2.me/theorems/0031e812-bd99-4437-a80c-2708189a720e
-- title:
--   Lemma 4.11: $\Phi_X(AO)(e)=A(H_Xe)\,\Phi_X(O)(e)$ for $A\in\mathcal A_X$ (both sectors)
-- statement:
--   If $A\in\mathcal A_X$ and $O=\bar XF\in V_X$ with $F\in\mathcal A_X$, then $AO\in V_X$ and for every $e\in\mathbb F_2^n$
--   $$\Phi_X(AO)(e)=A(H_Xe)\,\Phi_X(O)(e),$$
--   where $A(\cdot)$ is the syndrome eigenvalue function of $A$. The same holds in the Z sector: for $B\in\mathcal A_Z$ and $O=\bar ZF$, $F\in\mathcal A_Z$, $BO\in V_Z$ and $\Phi_Z(BO)(e)=B(H_Ze)\Phi_Z(O)(e)$.
--
--   Multiplication by a stabilizer-algebra element becomes multiplication by its syndrome eigenvalue function.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
--   - generalization: Φ_X : V_X → ℝ^{Ω_X} → Φ_X(O)(e) = (−1)^{ℓ_X·e}(X̄O)(H_X e), complex valued, for O = X̄A with any A in the complex algebra A_X; reason: A_X is a complex algebra and Φ_X is extended linearly; for Hermitian A the values are real and the statement specializes to the paper's
--   - generalization: X sector only → X- and Z-sector statements; reason: the Z clause is the X ↔ Z mirror the paper uses in Proposition 4.13 ("The analogous statements hold in the Z-sector"); dropping it gives the paper's statement
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.11, eq. (102), p. 36 (PDF p. 38)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_PhiX__43fab1
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.11 (Stabilizer algebra eigenvalue factorization).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.11, eq. (102),
p. 36 (PDF 38).

If `A ∈ A_X` and `O = X̄F ∈ V_X` with `F ∈ A_X`, then `AO ∈ V_X` and
`Φ_X(AO)(e) = A(H_X e) Φ_X(O)(e)`, where `A(·)` is the syndrome eigenvalue function (eq. (6)).
The second clause is the Z-sector analogue (`B ∈ A_Z`, `O = Z̄F`, `F ∈ A_Z`). -/
theorem lemma_4_11 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) :
    (∀ A ∈ C.algX, ∀ F ∈ C.algX, ∀ O : Op (n' + 1), O = pauliX Q.lX * F →
      Q.inVX (A * O) ∧ ∀ e, Q.PhiX (A * O) e = C.eigX A (C.HX *ᵥ e) * Q.PhiX O e) ∧
    (∀ B ∈ C.algZ, ∀ F ∈ C.algZ, ∀ O : Op (n' + 1), O = pauliZ Q.lZ * F →
      Q.inVZ (B * O) ∧ ∀ e, Q.PhiZ (B * O) e = C.eigZ B (C.HZ *ᵥ e) * Q.PhiZ O e) := by sorry

end AutoQMem.Lindblad
