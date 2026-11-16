-- Prove2me | Theorems.Thm_CatalystQLB_Query_Supplement_theorem_64
-- name    : CatalystQLB.Query.Supplement.theorem_64
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:03:18.721824+00:00
-- url     : https://prove2.me/theorems/faa45281-e46a-4d78-9c86-39bd7eaa7cd2
-- title:
--   Theorem 64 — an $\varepsilon$-approximately catalytic unitary with a pure catalyst acts on the system as a unitary up to $3\varepsilon^2/2$
-- statement:
--   Let $\mathcal H_{\mathrm{IO}}=(\mathbb C^2)^{\otimes n}$ and $\mathcal H_{\mathrm{catalyst}}=(\mathbb C^2)^{\otimes\ell}$. Let $0\le\varepsilon<1$, let $|\eta\rangle$ be a pure catalyst state on $\ell$ qubits, $\eta=|\eta\rangle\langle\eta|$, and let $U\in\mathcal U(n+\ell)$ be approximately catalytic for this catalyst: for every pure $|\phi\rangle\in\mathcal H_{\mathrm{IO}}$ there is a pure $|\psi\rangle\in\mathcal H_{\mathrm{IO}}$ with $\mathrm{TD}(U(\phi\otimes\eta)U^\dagger,\psi\otimes\eta)\le\varepsilon$. Then there is a single unitary $V_\eta\in\mathcal U(n)$ such that
--   $$\max_{\rho\in\mathrm{Den}(n)}\mathrm{TD}\big(C^\eta_U(\rho),\,C_{V_\eta}(\rho)\big)\le\frac{3\varepsilon^2}{2},$$
--   where $C^\eta_U(\rho)=\mathrm{tr}_{\mathrm{catalyst}}[U(\rho\otimes\eta)U^\dagger]$ and $C_{V_\eta}(\rho)=V_\eta\rho V_\eta^\dagger$.
--
--   Relaxing exact catalyst restoration to approximate restoration, even with residual correlations, therefore gives the input/output register essentially nothing beyond unitary dynamics in the information-theoretic setting. This is the formal version of the paper's Theorem 2.
--
--   **Formalization Note** The maximum over $\mathrm{Den}(n)$ is expressed as the bound for every density operator $\rho$ (mixed ones included), with $V_\eta$ chosen before $\rho$. $\mathrm{TD}$ is $\tfrac12\|\cdot\|_1$.
--
--   Differences from the source:
--   - encoding: max over ρ ∈ Den(n) of TD(C^η_U(ρ), C_{V_η}(ρ)) ≤ 3ε²/2 → ∃ V, ∀ ρ density, TD(C^η_U(ρ), C_V(ρ)) ≤ 3ε²/2; reason: a bound on the maximum is the same as the bound for every ρ; same instances
--   - encoding: U ∈ cat-U(n, ℓ, ε) with the catalyst state η = |η⟩⟨η| → a unit vector η with IsApproxCatalytic U (ketbra η) ε; reason: Definition 62's existential catalyst is the named witness |η⟩; same instances
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Theorem 64, Eq. (37), p.39 (PDF 42); informal restatement Theorem 2, p.5 (PDF 8)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_CatalystQLB_Query_Supplement_IsUnitVec
import Definitions.Def_CatalystQLB_Query_Supplement_ketbra
import Definitions.Def_CatalystQLB_Query_Supplement_TD
import Definitions.Def_CatalystQLB_Query_Supplement_catChannel
import Definitions.Def_CatalystQLB_Query_Supplement_unitaryChannel
import Definitions.Def_CatalystQLB_Query_Supplement_IsApproxCatalytic

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Theorem 64** (`C_{cat-U(n,ℓ,ε)} ≈_{ε²} C_{U(n)}`; Arora, Chakraborty, Cojocaru, Saminathan,
Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Theorem 64, Eq. (37), p.39 (PDF 42); stated informally as Theorem 2, p.5 (PDF 8)).
Let `0 ≤ ε < 1`, and let `U ∈ cat-U(n, ℓ, ε)` with the catalyst state `η = |η⟩⟨η| ∈ Den(ℓ)`.
Then there is a unitary `V_η ∈ U(n)` such that
`max_{ρ ∈ Den(n)} TD(C^η_U(ρ), C_{V_η}(ρ)) ≤ 3ε²/2`.

**Formalization Note** The pure catalyst is a unit vector `η` on the `ℓ` catalyst qubits, and
`U ∈ cat-U(n, ℓ, ε)` with that catalyst is `IsApproxCatalytic U (ketbra η) ε` (Definition 62 with
`|η⟩` as the witness). `V` is chosen before `ρ`; the maximum over `Den(n)` is the bound for every
density matrix `ρ` (mixed ones included). `TD` is `½‖·‖₁`. -/
theorem theorem_64 {n ℓ : ℕ} (U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
    (η : Qubits ℓ → ℂ) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hη : IsUnitVec η)
    (hU : IsApproxCatalytic U (ketbra η) ε) :
    ∃ V : Matrix.unitaryGroup (Qubits n) ℂ, ∀ ρ : Matrix (Qubits n) (Qubits n) ℂ,
      WildeQIT.IsDensityOperator ρ →
        TD (catChannel U (ketbra η) ρ) (unitaryChannel V ρ) ≤ 3 * ε ^ 2 / 2 := by sorry

end CatalystQLB.Query.Supplement
