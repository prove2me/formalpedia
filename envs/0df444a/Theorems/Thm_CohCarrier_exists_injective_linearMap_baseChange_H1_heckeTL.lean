-- Prove2me | Theorems.Thm_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL
-- name    : CohCarrier.exists_injective_linearMap_baseChange_H1_heckeTL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6ff70dd4-868c-55f1-b235-8e468f50550c
-- title:
--   Hecke-equivariant injection of base-changed H¹
-- statement:
--   Fix a natural number $M$ with $M \neq 0$ and a subgroup $H \le (\mathbb{Z}/M)^{\times}$, let $\mathcal{O}$ be a commutative ring that is a domain and a principal ideal ring, and let $K$ be a field equipped with an $\mathcal{O}$-algebra structure. For an additive coefficient group $A$, [`CohCarrier.H1 M H A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms from the additivisation of $\Gamma_H(M) =$ `GammaH M H` $\le \mathrm{SL}_2(\mathbb{Z})$ to $A$, and for $\ell \neq 0$ the operator [`CohCarrier.heckeTL M H A ℓ`](def/CohCarrier_Inst.html#L23) is the $\mathcal{O}$-linear endomorphism sending $\varphi$ to the transfer (`coresAdd`) of the pullback of $\varphi$ along the additivisation of the conjugation map `conjL M H ℓ` from `GammaHUpper M H ℓ` to $\Gamma_H(M)$. The assertion is the existence of a $K$-linear map $j : K \otimes_{\mathcal{O}} \mathrm{H}^1(M,H,\mathcal{O}) \to \mathrm{H}^1(M,H,K)$ such that: $j$ is injective; on pure tensors $j(c \otimes w) = c \cdot (\iota \circ w)$, where $\iota =$ `algebraMap 𝒪 K` viewed as an additive homomorphism; and $j$ intertwines the $K$-linear base change of `heckeTL M H 𝒪 ℓ` with `heckeTL M H K ℓ`, for every nonzero natural number $\ell$ (primality is not assumed) and every $x$ in the tensor product.
--
--   This is the universal-coefficients comparison for the first cohomology of $\Gamma_H(M)$ with trivial coefficients, in the Hecke-equivariant form needed to pass from a base-changed cohomology module to genuine $K$-valued homomorphisms $\Gamma_H(M) \to K$. It is used in the construction of Hecke characters on corner rings arising from idempotent splittings and in the comparison of Hecke operators with auxiliary-level operators in the Taylor–Wiles patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CohCarrier.exists_injective_linearMap_baseChange_H1_heckeTL
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] :
    ∃ j : K ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[K] CohCarrier.H1 M H K,
      Function.Injective j ∧
      (∀ (c : K) (w : CohCarrier.H1 M H 𝒪),
        j (c ⊗ₜ[𝒪] w) = c • ((algebraMap 𝒪 K).toAddMonoidHom.comp w)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (x : K ⊗[𝒪] CohCarrier.H1 M H 𝒪),
        j (((CohCarrier.heckeTL M H 𝒪 ℓ).baseChange K) x) =
          CohCarrier.heckeTL M H K ℓ (j x) := by sorry
