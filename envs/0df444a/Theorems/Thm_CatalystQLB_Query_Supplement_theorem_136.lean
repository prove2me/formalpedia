-- Prove2me | Theorems.Thm_CatalystQLB_Query_Supplement_theorem_136
-- name    : CatalystQLB.Query.Supplement.theorem_136
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:04:51.650946+00:00
-- url     : https://prove2.me/theorems/79247c76-03bf-4dde-b35c-76d39059d989
-- title:
--   Theorem 136 — with a mixed catalyst, an $\varepsilon$-approximately catalytic unitary acts as a unitary up to $18\varepsilon$
-- statement:
--   Let $0\le\varepsilon<1/18$, fix a catalyst state $\eta\in\mathrm{Den}(\ell)$ (possibly mixed), and let $U\in\mathsf{cat}\text{-}\mathcal U_\eta(n,\ell,\varepsilon)$: for every pure $|\phi\rangle\in\mathcal H_{\mathrm{IO}}$ there is a pure $|\psi\rangle\in\mathcal H_{\mathrm{IO}}$ with $\mathrm{TD}(U(\phi\otimes\eta)U^\dagger,\psi\otimes\eta)\le\varepsilon$. Then there is a fixed unitary $V_\eta\in\mathcal U(n)$ such that
--   $$\max_{\rho\in\mathrm{Den}(n)}\mathrm{TD}\big(C^\eta_U(\rho),\,C_{V_\eta}(\rho)\big)\le18\,\varepsilon .$$
--
--   This extends Theorem 64 from pure to mixed catalysts, with a bound linear instead of quadratic in $\varepsilon$: approximately restored mixed catalysts still offer no information-theoretic advantage on the input/output register.
--
--   **Formalization Note** $\eta$ is an arbitrary density operator on the catalyst, not the paper's specific state $\eta_{\ell,p}$. The maximum over $\mathrm{Den}(n)$ is the bound for every density operator $\rho$, with $V_\eta$ chosen before $\rho$; $\mathrm{TD}$ is $\tfrac12\|\cdot\|_1$.
--
--   Differences from the source:
--   - encoding: max over ρ ∈ Den(n) of TD(C^η_U(ρ), C_{V_η}(ρ)) ≤ 18ε → ∃ V, ∀ ρ density, TD(C^η_U(ρ), C_V(ρ)) ≤ 18ε; reason: a bound on the maximum is the same as the bound for every ρ; same instances
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Theorem 136, Eq. (150), p.92 (PDF 95); Definition 115, Eq. (71), p.69 (PDF 72)

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

/-- **Theorem 136** (Approximate catalytic channels with a mixed catalyst; Arora, Chakraborty,
Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*,
arXiv:2609.40323 (version of 2026-11-03), Theorem 136, Eq. (150), p.92 (PDF 95)).
Let `0 ≤ ε < 1/18`, fix `η ∈ Den(ℓ)`, and let `U ∈ cat-U_η(n, ℓ, ε)`. There is a fixed unitary
`V_η ∈ U(n)` such that `max_{ρ ∈ Den(n)} TD(C^η_U(ρ), C_{V_η}(ρ)) ≤ 18ε`.

**Formalization Note** `η` is an arbitrary (possibly mixed) density matrix on the catalyst, not
the paper's `η_{ℓ,p}`. `U ∈ cat-U_η(n, ℓ, ε)` is `IsApproxCatalytic U η ε` (Eq. (71)). `V` is
chosen before `ρ`; the maximum over `Den(n)` is the bound for every density matrix `ρ`.
`TD` is `½‖·‖₁`. -/
theorem theorem_136 {n ℓ : ℕ} (U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
    (η : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 18)
    (hη : WildeQIT.IsDensityOperator η) (hU : IsApproxCatalytic U η ε) :
    ∃ V : Matrix.unitaryGroup (Qubits n) ℂ, ∀ ρ : Matrix (Qubits n) (Qubits n) ℂ,
      WildeQIT.IsDensityOperator ρ →
        TD (catChannel U η ρ) (unitaryChannel V ρ) ≤ 18 * ε := by sorry

end CatalystQLB.Query.Supplement
