-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_proposition_4_16
-- name    : AutoQMem.Lindblad.proposition_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:11.793169+00:00
-- url     : https://prove2.me/theorems/520ad61b-560c-43a6-9558-cba61fa0681b
-- title:
--   Proposition 4.16: $\tfrac12(\lambda_X+\lambda_Z)\le F_{\min}[\mathcal W_*]\le\tfrac12(1+\min_\sigma\lambda_\sigma)$
-- statement:
--   Under the hypotheses of Lemma 4.15 (a CPTP map $\mathcal W_*$ whose Heisenberg adjoint is covariant under conjugation by $\bar X$ and $\bar Z$),
--   $$\tfrac12\Bigl(\langle T_X,\mathcal W^*(T_X)\rangle_{\mathrm{code}}+\langle T_Z,\mathcal W^*(T_Z)\rangle_{\mathrm{code}}\Bigr)\le F_{\min}[\mathcal W_*]\le\tfrac12\Bigl(1+\min_{\sigma\in\{X,Z\}}\langle T_\sigma,\mathcal W^*(T_\sigma)\rangle_{\mathrm{code}}\Bigr).$$
--
--   The two decoded-logical autocorrelations bound the worst-case encoded fidelity from both sides.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
--   - encoding: the real autocorrelations ⟨T_σ, W^*(T_σ)⟩_code → their real parts; reason: under the hypotheses they are real (Lemma 4.15), so the real part changes nothing
--   - encoding: F_min = min over unit |ψ⟩ ∈ H_Q → infimum over ψ ∈ ℂ² with Σ|ψ_i|² = 1; reason: the fidelity of a CPTP map is continuous on the unit sphere, so the infimum is attained
--   - encoding: F(ψ; W_*) = ⟨ψ| E_L[W_*](|ψ⟩⟨ψ|) |ψ⟩ → its real part; reason: E_L[W_*] is a channel for CPTP W_*, so the value is real and the real part changes nothing
--   - encoding: CPTP map W_* →AKNMixed.FQP.IsQuantumOperation (published; linear, trace preserving, completely positive via T ⊗ id_k); reason: the standard definition in finite dimension
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Proposition 4.16, eq. (119), p. 40 (PDF p. 42)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_Fmin
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_TX
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_codeInner
import Definitions.Def_AutoQMem_Lindblad_hsAdj
import Definitions.Def_AKNMixed_FQP_IsQuantumOperation
open Matrix

namespace AutoQMem.Lindblad

/-- **Proposition 4.16 (Worst-case fidelity bounds from logical autocorrelations).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Proposition 4.16, eq. (119), p. 40 (PDF 42).

Under the hypotheses of Lemma 4.15,
`½(⟨T_X, W^*(T_X)⟩_code + ⟨T_Z, W^*(T_Z)⟩_code) ≤ F_min[W_*] ≤ ½(1 + min_{σ∈{X,Z}} ⟨T_σ, W^*(T_σ)⟩_code)`.

**Formalization Note.** The autocorrelations are real under these hypotheses (Lemma 4.15); their
real parts are compared. -/
theorem proposition_4_16 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (T : Op (n' + 1) → Op (n' + 1)) (hT : AKNMixed.FQP.IsQuantumOperation T)
    (hcovX : ∀ O : Op (n' + 1),
      hsAdj T (pauliX Q.lX * O * pauliX Q.lX) = pauliX Q.lX * hsAdj T O * pauliX Q.lX)
    (hcovZ : ∀ O : Op (n' + 1),
      hsAdj T (pauliZ Q.lZ * O * pauliZ Q.lZ) = pauliZ Q.lZ * hsAdj T O * pauliZ Q.lZ) :
    (1 / 2 : ℝ) * ((Q.codeInner (Q.TX DX) (hsAdj T (Q.TX DX))).re +
        (Q.codeInner (Q.TZ DZ) (hsAdj T (Q.TZ DZ))).re) ≤ Q.Fmin DX DZ T ∧
      Q.Fmin DX DZ T ≤ (1 / 2 : ℝ) * (1 + min (Q.codeInner (Q.TX DX) (hsAdj T (Q.TX DX))).re
        (Q.codeInner (Q.TZ DZ) (hsAdj T (Q.TZ DZ))).re) := by sorry

end AutoQMem.Lindblad
