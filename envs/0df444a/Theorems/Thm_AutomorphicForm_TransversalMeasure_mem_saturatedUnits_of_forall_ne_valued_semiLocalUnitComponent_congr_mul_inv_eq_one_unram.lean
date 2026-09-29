-- Prove2me | Theorems.Thm_AutomorphicForm_TransversalMeasure_mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram
-- name    : AutomorphicForm.TransversalMeasure.mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/f5a94060-3249-59cb-aeff-88843415db6c
-- title:
--   Saturation criterion at an unramified place, cyclic case
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, and let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a nonzero prime of $\mathcal O_K$, and assume that every nonzero prime $w$ of $\mathcal O_L$ with $w$ lying over $v$ satisfies $\mathrm{ramificationIdx}'(v, w) = 1$. Let $u$ be a unit of $L \otimes_K K_v$, where $K_v$ is the $v$-adic completion of $K$, and let $w_0$ be a prime of $\mathcal O_L$ over $v$. Write $a := (\sigma \otimes \mathrm{id}_{K_v})(u)\, u^{-1}$, the image of $u$ under the unit-group map induced by `Algebra.TensorProduct.congr` of $\sigma$ with the identity of $K_v$, multiplied by $u^{-1}$. Assume that for every prime $w$ of $\mathcal O_L$ over $v$ with $w \neq w_0$, the $w$-component of $a$ under the $L$-algebra isomorphism $L \otimes_K K_v \simeq \prod_{w \mid v} L_w$ has valuation $1$. The conclusion is that $u$ lies in the set product of the unit group of the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v` with the image of $K_v^\times$ under the map induced by `Algebra.TensorProduct.includeRight`; that is, $u$ is an integral unit times an element of $K_v^\times$ embedded on the right factor.
--
--   This is the local saturation step at a finite place unramified in $L$: a single place above $v$ may be ignored when testing integrality of the twisted commutator $(\sigma \otimes 1)(u)u^{-1}$, because the valuations of the components of $u$ are then forced to be equal and a uniformiser of $K_v$ is a uniformiser at each $w$. It is used in the twisted Bruhat computation, in [`AutomorphicForm.TwistedBruhat.apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram`](thm.html#AutomorphicForm.TwistedBruhat.apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram), to see that certain unipotent terms vanish away from the saturated units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TransversalMeasure_mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.TransversalMeasure.mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal = 1)
    (u : (L ⊗[K] v.adicCompletion K)ˣ) (w₀ : v.Extension (𝓞 L))
    (h : ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
      Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w
        (Units.mapEquiv (Algebra.TensorProduct.congr σ
            (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv u * u⁻¹) :
          (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) = 1) :
    u ∈ AutomorphicForm.TransversalMeasure.saturatedUnits K L v := by sorry
