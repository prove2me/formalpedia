-- Prove2me | Theorems.Thm_CatalystQLB_Query_Supplement_theorem_86
-- name    : CatalystQLB.Query.Supplement.theorem_86
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:04:08.814478+00:00
-- url     : https://prove2.me/theorems/68160ea7-c94f-4bb3-988a-c0bac7c2d078
-- title:
--   Theorem 86 — catalytic ergotropy equals ergotropy: $\mathrm{erg}_{\rho,H}=\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}$
-- statement:
--   For every number of qubits $n$, every state $\rho\in\mathrm{Den}(n)$ and every Hamiltonian $H\in\mathrm{Herm}(n)$,
--   $$\mathrm{erg}_{\rho,H}=\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}.$$
--   Here $\mathrm{erg}_{\rho,H}=\max_{U\in\mathcal U(n)}\mathrm{tr}[H(\rho-U\rho U^\dagger)]$ is the ergotropy, and $\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}=\max_{\ell\ge0}\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}(\ell)$ is the catalytic ergotropy, the maximum over any number $\ell$ of catalyst qubits, any pure catalyst $|\eta\rangle$ on them and any unitary that restores $|\eta\rangle$ exactly, of the energy extracted with Hamiltonian $H\otimes I$.
--
--   In the information-theoretic setting a catalyst therefore does not increase the maximum extractable work; the paper's separations between ergotropy and its catalytic variants are purely computational.
--
--   Differences from the source:
--   - reading: Definition 84 prints ρ ⊗ |η⟩⟨η|^{⊗ℓ} → ρ ⊗ |η⟩⟨η| with |η⟩ a unit vector on the ℓ catalyst qubits; reason: |η⟩ ∈ H_catalyst already has ℓ qubits, so the tensor power is a typo; the proof of Theorem 86 uses ρ ⊗ |η⟩⟨η|
--   - reading: ∀h ∈ Ham(n) in the display → H Hermitian (H ∈ Herm(n)); reason: the theorem's first sentence fixes H ∈ Herm(n); Ham(n) and h are the same object
--   - encoding: maxima in Definitions 13 and 84 → real suprema ⨆ over the stated sets; reason: the sets are nonempty and bounded for density ρ and Hermitian H, so the supremum is the maximum; same value
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Theorem 86, p.53 (PDF 56); Definitions 13 (p.19, PDF 22), 65 (p.40, PDF 43) and 84 (p.53, PDF 56)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_CatalystQLB_Query_Supplement_erg
import Definitions.Def_CatalystQLB_Query_Supplement_catErg

open scoped Matrix

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Theorem 86** (Equivalence of `erg` and `cat-erg`; Arora, Chakraborty, Cojocaru, Saminathan,
Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Theorem 86, p.53 (PDF 56)). For every system size `n`, state `ρ ∈ Den(n)` and
Hamiltonian `H ∈ Herm(n)`, the maximum extractable work is unchanged by the assistance of a
catalytic system: `erg_{ρ,H} = cat-erg_{ρ,H}`.

**Formalization Note** `cat-erg_{ρ,H}` is the supremum over all catalyst sizes `ℓ ≥ 0`, all unit
`|η⟩` on `ℓ` qubits and all exact catalytic unitaries `U ∈ cat-U_{|η⟩}(n, ℓ)` (Definitions 65,
84); `erg` is Definition 13 on `U(n)`. The display's `∀h ∈ Ham(n)` is the theorem's `H ∈ Herm(n)`. -/
theorem theorem_86 (n : ℕ) (ρ H : Matrix (Qubits n) (Qubits n) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hH : H.IsHermitian) :
    erg ρ H = catErg n ρ H := by sorry

end CatalystQLB.Query.Supplement
