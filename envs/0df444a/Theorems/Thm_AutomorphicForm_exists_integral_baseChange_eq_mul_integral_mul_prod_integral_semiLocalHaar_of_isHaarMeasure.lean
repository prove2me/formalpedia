-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure
-- name    : AutomorphicForm.exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/04e297d7-9411-5de7-81fd-1edeff1471f4
-- title:
--   Haar measure on GL₂(L⊗_KA_K) factorises over places of K
-- statement:
--   Let $K\subseteq L$ be number fields, and give $GL_2$ of each of the rings $L\otimes_K\mathbb{A}_K$, $L\otimes_K K_\infty$ and $L\otimes_K K_v$ the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) of its topology. Let $\mu$ be a Haar measure on $GL_2(L\otimes_K\mathbb{A}_K)$ and $\nu$ a Haar measure on $GL_2(L\otimes_K K_\infty)$, where $\mathbb{A}_K$ is the adele ring of $K$ and $K_\infty$ its infinite adele ring. Then there is a real $c>0$ such that the following holds for every finite set $S$ of height-one primes of $\mathcal{O}_K$ and all functions $F$ on $GL_2(L\otimes_K\mathbb{A}_K)$, $F_a$ on $GL_2(L\otimes_K K_\infty)$ and $F_v$ on $GL_2(L\otimes_K K_v)$ (one for every height-one prime $v$), all complex valued: if $F_a$ is almost everywhere strongly measurable for $\nu$, each $F_v$ with $v\in S$ is almost everywhere strongly measurable for [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) — the Haar measure normalised to give mass $1$ to the set of $g\in GL_2(L\otimes_K K_v)$ for which both $g$ and $g^{-1}$ have matrices in `integralMatrixSet` of the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v` —, if $F(x)=F_a(x_\infty)\prod_{v\in S}F_v(x_v)$ whenever $x_v$ lies in that integral set for all $v\notin S$, and $F(x)=0$ as soon as $x_v$ fails to lie in it for some $v\notin S$, then $\int F\,d\mu = c\,\bigl(\int F_a\,d\nu\bigr)\prod_{v\in S}\int F_v\,d(\mathrm{semiLocalHaar}\ K\ L\ v)$. Here $x_\infty$ and $x_v$ denote the images of $x$ under the maps [`AutomorphicForm.tensorArch K L`](def/AutomorphicForm_BaseChangePlaces.html#L46) and [`AutomorphicForm.tensorPlace K L v`](def/AutomorphicForm_BaseChangePlaces.html#L49) induced on $GL_2$ by $\mathrm{id}_L\otimes$ the archimedean, resp. the $v$-adic, projection of $\mathbb{A}_K$. No measurability hypothesis is imposed on $F$ itself.
--
--   This is the measure-theoretic comparison of a Haar measure on the base-changed group $GL_2(L\otimes_K\mathbb{A}_K)\cong GL_2(\mathbb{A}_L)$ with the product of an archimedean Haar measure and the restricted product, over the finite places $v$ of the ground field $K$, of the Haar measures on $GL_2(L\otimes_K K_v)$ normalised by giving mass one to the integral subgroups; the constant is independent of $S$ precisely because of that normalisation. It is used to evaluate global integrals of factorisable functions on $GL_2(L\otimes_K\mathbb{A}_K)$ place by place, in the construction of matching functions at a prime and in the computation of twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v)
          (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) *
              ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = 0) →
          ∫ x, F x ∂μ = c * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v) := by sorry
