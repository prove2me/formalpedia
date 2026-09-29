-- Prove2me | Theorems.Thm_CohCarrier_exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
-- name    : CohCarrier.exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/3a5c1725-1046-5a37-baaa-d0d53b38f85e
-- title:
--   Base change of Γ_H(N)-homomorphisms along 𝒪→ F
-- statement:
--   Let $\mathcal O$ be a commutative ring which is a domain and a principal ideal ring, let $F$ be a field equipped with an $\mathcal O$-algebra structure such that the structure map $\mathcal O\to F$ is injective, let $N$ be a nonzero natural number and let $H$ be a subgroup of $(\mathbb Z/N)^\times$. Write $\Gamma=$ [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb Z)$ obtained by pulling back $H$ along the homomorphism `gamma0Units` $\Gamma_0(N)\to(\mathbb Z/N)^\times$ (given by the lower right entry mod $N$) and pushing forward along the inclusion $\Gamma_0(N)\hookrightarrow\mathrm{SL}_2(\mathbb Z)$, and for an abelian group $A$ write $H^1=$ [`CohCarrier.H1 N H A`](def/CohCarrier_Level.html#L162) for the group of additive homomorphisms $\mathrm{Additive}(\Gamma)\to A$, i.e. homomorphisms $\Gamma\to A$. The assertion is that there exists an $F$-linear equivalence $\Phi\colon F\otimes_{\mathcal O}H^1(\Gamma,\mathcal O)\xrightarrow{\ \sim\ }H^1(\Gamma,F)$ with three properties. First, $\Phi$ is given on pure tensors by $\Phi(x\otimes\varphi)=x\cdot(\varphi$ followed by $\mathcal O\to F)$. Second, for every nonzero natural number $\ell$, $\Phi$ intertwines the base change to $F$ of [`CohCarrier.heckeTL N H 𝒪 ℓ`](def/CohCarrier_Inst.html#L23) with [`CohCarrier.heckeTL N H F ℓ`](def/CohCarrier_Inst.html#L23), where `heckeTL ℓ` is the endomorphism of $H^1$ sending $\varphi$ to the transfer (corestriction) to $\Gamma$ of the composite of $\varphi$ with the homomorphism `conjL` from the finite-index subgroup `GammaHUpper N H ℓ` to $\Gamma$ induced by conjugation by the upper triangular matrix attached to $\ell$. Third, $\Phi$ carries the range of the base change to $F$ of the inclusion of [`ModularCurve.Period.parabolicHoms 𝒪 Γ 𝒪`](def/ModularCurve_PeriodMap.html#L62) into $H^1(\Gamma,\mathcal O)$ exactly onto [`ModularCurve.Period.parabolicHoms F Γ F`](def/ModularCurve_PeriodMap.html#L62), where `parabolicHoms` denotes the submodule of those homomorphisms that vanish on every $\gamma\in\Gamma$ whose matrix satisfies $\mathrm{tr}(\gamma)^2=4$.
--
--   This is the flat base change statement for the group-cohomological carrier $\mathrm{Hom}(\Gamma_H(N),-)$ along an embedding of a principal ideal domain into a field, asserting simultaneously compatibility with the transfer Hecke operators $T_\ell$ (respectively $U_\ell$ for $\ell\mid N$) and with the submodule of parabolic classes. It is the passage between integral and characteristic-zero or residual coefficients used in the computation of the rank of a Hecke eigenspace in a corner submodule and in the production of an algebra homomorphism to an algebraic closure realising a residual Hecke system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem CohCarrier.exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (F : Type) [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    ∃ Φ : F ⊗[𝒪] CohCarrier.H1 N H 𝒪 ≃ₗ[F] CohCarrier.H1 N H F,
      (∀ (x : F) (φ : CohCarrier.H1 N H 𝒪),
        Φ (x ⊗ₜ[𝒪] φ) = x • ((algebraMap 𝒪 F).toAddMonoidHom.comp φ)) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (v : F ⊗[𝒪] CohCarrier.H1 N H 𝒪),
        Φ ((CohCarrier.heckeTL N H 𝒪 ℓ).baseChange F v) = CohCarrier.heckeTL N H F ℓ (Φ v)) ∧
      Submodule.map (Φ : F ⊗[𝒪] CohCarrier.H1 N H 𝒪 →ₗ[F] CohCarrier.H1 N H F)
          (LinearMap.range ((ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N H) 𝒪).subtype.baseChange F)) =
        ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N H) F := by sorry
