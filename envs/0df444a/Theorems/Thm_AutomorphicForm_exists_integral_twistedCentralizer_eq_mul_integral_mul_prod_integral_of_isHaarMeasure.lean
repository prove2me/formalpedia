-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
-- name    : AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/d3808f96-f0f5-57c2-b168-e51cafb87d1f
-- title:
--   Haar measure on a twisted centralizer factorises over the places
-- statement:
--   Let $K \subseteq L$ be number fields, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$. For a commutative topological $K$-algebra $A$ write $T'(A)$ for the subgroup $\{t : t\,\delta_A\,\sigma_{\mathrm{GL}}(t)^{-1} = \delta_A\}$ of $\mathrm{GL}_2(L \otimes_K A)$, where $\sigma_{\mathrm{GL}}$ acts entrywise through the first tensor factor, equipped with its Borel $\sigma$-algebra; here $\delta_A$ is the image of $\delta$ under $\mathrm{GL}_2$ of $\mathrm{id}_L \otimes$ (projection), namely `tensorArch` to $A = K_\infty$ and `tensorPlace` at a finite place $v$ to $A = K_v$. Assume given a Haar measure $\tau$ on $T'(\mathbb{A}_K)$, a Haar measure $\tau_\infty$ on $T'(K_\infty)$, and for every $v \in$ `HeightOneSpectrum` $(\mathcal{O}_K)$ a Haar measure $\tau_v$ on $T'(K_v)$ with $\tau_v$ of the set of $t$ whose underlying matrix and whose inverse both have entries in the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v` equal to $1$. Then there is a real $c > 0$ such that for every finite set $S$ of finite places and all functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, $W_\infty$ on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and $W_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$ such that $W_\infty$ is a.e. strongly measurable for $\tau_\infty$, each $W_v$ with $v \in S$ is a.e. strongly measurable for $\tau_v$, every $t \in T'(\mathbb{A}_K)$ which is integral at all $v \notin S$ in the above sense satisfies $W(t) = W_\infty(t_\infty)\prod_{v \in S} W_v(t_v)$, and $W(t) = 0$ whenever $t$ fails to be integral at some $v \notin S$, one has $\int_{T'(\mathbb{A}_K)} W \,\mathrm{d}\tau = c \left(\int_{T'(K_\infty)} W_\infty \,\mathrm{d}\tau_\infty\right) \prod_{v \in S} \int_{T'(K_v)} W_v \,\mathrm{d}\tau_v$. The constant $c$ is chosen before $S$ and the functions, so it is independent of them.
--
--   This is the statement, in integral form, that the $\sigma$-twisted centralizer of $\delta$ over the adeles is the restricted product over the places of $K$ of the local twisted centralizers, with the local measures normalised by the semi-local integral subgroups, so that a global Haar measure is a positive multiple of the product of the local ones. It is the measure-theoretic input to the construction of matching functions for twisted orbital integrals over the adele ring from local matching data at the finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by sorry
