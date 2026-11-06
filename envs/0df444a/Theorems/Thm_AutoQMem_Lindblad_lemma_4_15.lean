-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_15
-- name    : AutoQMem.Lindblad.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:50.611222+00:00
-- url     : https://prove2.me/theorems/64b43133-558b-45ba-b475-5744e49c834f
-- title:
--   Lemma 4.15: $\bar X$-, $\bar Z$-covariant CPTP dynamics give a Pauli effective channel with $\lambda_\sigma=\langle T_\sigma,\mathcal W^*(T_\sigma)\rangle_{\mathrm{code}}$
-- statement:
--   Let $\mathcal W_*$ be a CPTP map on $\mathcal B(\mathcal H)$ whose Heisenberg adjoint satisfies
--   $$\mathcal W^*(\bar PO\bar P)=\bar P\,\mathcal W^*(O)\,\bar P,\qquad \bar P\in\{\bar X,\bar Z\},$$
--   for every operator $O$. Then the effective logical channel $\mathcal E_L[\mathcal W_*]$ is a Pauli channel: there are $p_I,p_X,p_Y,p_Z\ge0$ with $\sum_Pp_P=1$ and
--   $$\mathcal E_L[\mathcal W_*](\rho)=\sum_{P\in\{I,X,Y,Z\}}p_P\,P\rho P .$$
--   Equivalently, $\mathcal E_L^*[\mathcal W_*](X_Q)=\lambda_XX_Q$, $\mathcal E_L^*[\mathcal W_*](Y_Q)=\lambda_YY_Q$, $\mathcal E_L^*[\mathcal W_*](Z_Q)=\lambda_ZZ_Q$. Moreover
--   $$\lambda_X=\langle T_X,\mathcal W^*(T_X)\rangle_{\mathrm{code}},\qquad \lambda_Z=\langle T_Z,\mathcal W^*(T_Z)\rangle_{\mathrm{code}} .$$
--
--   The X and Z eigenvalues of the effective channel are the decoded-logical autocorrelations, which converts classical memory bounds into fidelity bounds.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
--   - encoding: CPTP map W_* : T(H) → T(H) → AKNMixed.FQP.IsQuantumOperation (published): ℂ-linear, trace preserving on every matrix, completely positive via T ⊗ id_k for every k; reason: the standard definition in finite dimension
--   - reading: eigenvalues λ_X, λ_Y, λ_Z (field unspecified) → λ_X, λ_Y, λ_Z real numbers; reason: the eigenvalues of a Pauli channel are real (λ_X = p_I + p_X − p_Y − p_Z, used in the proof of Proposition 4.16); this reading is the stronger one
--   - encoding: Pauli channel Σ_P p_P P ρ P → Σ_P p_P P ρ P†; reason: the Pauli matrices are Hermitian
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.15, eqs. (116)–(118), p. 39 (PDF p. 41); proof Appendix B, pp. 68–69 (PDF pp. 70–71)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_effective
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_TX
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_codeInner
import Definitions.Def_AutoQMem_Lindblad_hsAdj
import Definitions.Def_AKNMixed_FQP_IsQuantumOperation
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.15 (Pauli covariance and the effective logical channel).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.15,
eqs. (116)–(118), p. 39 (PDF 41); proof Appendix B, pp. 68–69 (PDF 70–71).

Let `W_*` be a CPTP map whose Heisenberg adjoint satisfies `W^*(P̄ O P̄) = P̄ W^*(O) P̄` for
`P̄ ∈ {X̄, Z̄}` and every `O`. Then the effective logical channel `E_L[W_*]` is a Pauli channel,
`E_L[W_*](ρ) = Σ_P p_P P ρ P` with `p_P ≥ 0`, `Σ_P p_P = 1`; equivalently
`E_L^*[W_*](X_Q) = λ_X X_Q`, `E_L^*[W_*](Y_Q) = λ_Y Y_Q`, `E_L^*[W_*](Z_Q) = λ_Z Z_Q`. Moreover
`λ_X = ⟨T_X, W^*(T_X)⟩_code` and `λ_Z = ⟨T_Z, W^*(T_Z)⟩_code`.

**Formalization Note.** `W^* = hsAdj T`, `E_L^*[W_*] = hsAdj (effective T)`. The eigenvalues
`λ_P` are real numbers (as for every Pauli channel). The Pauli channel is written with
`P ρ P†` (`= P ρ P`, the Paulis being Hermitian). -/
theorem lemma_4_15 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (T : Op (n' + 1) → Op (n' + 1)) (hT : AKNMixed.FQP.IsQuantumOperation T)
    (hcovX : ∀ O : Op (n' + 1),
      hsAdj T (pauliX Q.lX * O * pauliX Q.lX) = pauliX Q.lX * hsAdj T O * pauliX Q.lX)
    (hcovZ : ∀ O : Op (n' + 1),
      hsAdj T (pauliZ Q.lZ * O * pauliZ Q.lZ) = pauliZ Q.lZ * hsAdj T O * pauliZ Q.lZ) :
    (∃ p : Pauli1 → ℝ, (∀ P, 0 ≤ p P) ∧ ∑ P, p P = 1 ∧
      ∀ ρQ : Matrix (ZMod 2) (ZMod 2) ℂ,
        Q.effective DX DZ T ρQ = ∑ P, (p P : ℂ) • (Pauli1.sigma P * ρQ * (Pauli1.sigma P)ᴴ)) ∧
    (∃ lamX lamY lamZ : ℝ,
      hsAdj (Q.effective DX DZ T) (Pauli1.sigma .X) = (lamX : ℂ) • Pauli1.sigma .X ∧
      hsAdj (Q.effective DX DZ T) (Pauli1.sigma .Y) = (lamY : ℂ) • Pauli1.sigma .Y ∧
      hsAdj (Q.effective DX DZ T) (Pauli1.sigma .Z) = (lamZ : ℂ) • Pauli1.sigma .Z ∧
      (lamX : ℂ) = Q.codeInner (Q.TX DX) (hsAdj T (Q.TX DX)) ∧
      (lamZ : ℂ) = Q.codeInner (Q.TZ DZ) (hsAdj T (Q.TZ DZ))) := by sorry

end AutoQMem.Lindblad
