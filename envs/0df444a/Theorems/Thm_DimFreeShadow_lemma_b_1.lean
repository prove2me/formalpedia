-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_b_1
-- name    : DimFreeShadow.lemma_b_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:52.771218+00:00
-- url     : https://prove2.me/theorems/71584f8b-b54f-40e6-bc3b-7ed9acf02bc0
-- title:
--   Lemma B.1 — supports of marginals, the variational trace distance, Fuchs–van de Graaf
-- statement:
--   For every bipartite state $\omega_{UV}$,
--
--   $$
--   \operatorname{supp}\omega_{UV}\subseteq\operatorname{supp}\omega_U\otimes\operatorname{supp}\omega_V .
--   $$
--
--   For density matrices $\rho,\sigma$ on the same space,
--
--   $$
--   d_{\mathrm{tr}}(\rho,\sigma)=\max_{0\preceq E\preceq I}|\operatorname{Tr}(E(\rho-\sigma))| .
--   $$
--
--   Trace distance contracts under quantum channels, and $d_{\mathrm{tr}}(\rho,\sigma)\le\sqrt{1-F(\rho,\sigma)^2}$, with $F$ the root fidelity.
--
--   These four facts convert the fidelity bound of Theorem 4.2 into the expectation bound used in Lemma 4.3.
--
--   Differences from the source:
--   - encoding: supp ω_UV ⊆ supp ω_U ⊗ supp ω_V → (Π_{supp ω_U} ⊗ Π_{supp ω_V}) ω_UV = ω_UV; reason: for a positive semidefinite ω_UV this says exactly that its support lies in the product subspace
--   - encoding: d_tr(ρ, σ) = max over effects of |Tr(E(ρ − σ))| → an upper bound over all effects, together with an effect attaining it; reason: this is what a maximum means; it avoids the junk value of a real supremum
--   - encoding: the absolute value |Tr(E(ρ − σ))| of a real trace → the complex modulus ‖Tr(E(ρ − σ))‖; reason: Tr(E(ρ − σ)) is real for Hermitian E and ρ − σ, so the modulus is its absolute value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma B.1, p.35

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_WildeQIT_Recover_spectralFun
import Definitions.Def_DimFreeShadow_traceDistance

namespace DimFreeShadow

/-- **Lemma B.1** (arXiv:2608.06345, sha256 a1a42249…, Lemma B.1, p.35). (38) For every
bipartite state `ω_{UV}`, `supp ω_{UV} ⊆ supp ω_U ⊗ supp ω_V`. (39) For density matrices
`ρ, σ`, `d_tr(ρ, σ) = max_{0⪯E⪯I} |Tr(E(ρ − σ))|`. Trace distance contracts under quantum
channels, and (40) `d_tr(ρ, σ) ≤ √(1 − F(ρ, σ)²)` with the root fidelity `F`.

**Formalization Note** (38) is stated as `(Π_{supp ω_U} ⊗ Π_{supp ω_V}) ω_{UV} = ω_{UV}`, which
for a positive semidefinite `ω_{UV}` says exactly that its support lies in
`supp ω_U ⊗ supp ω_V`; `ω_U = traceRight ω`, `ω_V = traceLeft ω` (published
`QAlgorithms` partial traces), `⊗` is the Kronecker product. The maximum in (39) is stated as
an upper bound over all effects together with an effect attaining it; `|·|` is the complex
modulus. Channels are `QAlgorithms.IsChannel` (finite Kraus form) between possibly different
spaces. `F` is `WildeQIT.rootFidelity` (`‖√ρ√σ‖₁`). -/
theorem lemma_b_1 {U V n m : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] :
    (∀ ω : Matrix (U × V) (U × V) ℂ, WildeQIT.IsDensityOperator ω →
      Matrix.kroneckerMap (· * ·) (WildeQIT.Recover.supportProj (QAlgorithms.traceRight ω))
        (WildeQIT.Recover.supportProj (QAlgorithms.traceLeft ω)) * ω = ω) ∧
    (∀ ρ σ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator σ →
      (∀ E : Matrix n n ℂ, QAlgorithms.IsEffect E →
        ‖(E * (ρ - σ)).trace‖ ≤ traceDistance ρ σ) ∧
      ∃ E : Matrix n n ℂ, QAlgorithms.IsEffect E ∧ ‖(E * (ρ - σ)).trace‖ = traceDistance ρ σ) ∧
    (∀ Φ : QAlgorithms.Superop n m, QAlgorithms.IsChannel Φ →
      ∀ ρ σ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator σ →
        traceDistance (Φ ρ) (Φ σ) ≤ traceDistance ρ σ) ∧
    (∀ ρ σ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator σ →
      traceDistance ρ σ ≤ Real.sqrt (1 - WildeQIT.rootFidelity ρ σ ^ 2)) := by sorry

end DimFreeShadow
