-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant
-- name    : AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/68a50930-280b-5d9d-a31f-7b34f0f081a0
-- title:
--   Local twisted section functions from a global one
-- statement:
--   Let $K\subseteq L$ be number fields, $\sigma$ a $K$-automorphism of $L$, acting on $\mathrm{GL}_2(L\otimes_K A)$ through $\sigma\otimes\mathrm{id}$, and let $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$. Write $\delta_v$, $\delta_\infty$ for the images of $\delta$ under the maps induced by $\mathbb{A}_K\to K_v$ and $\mathbb{A}_K\to\mathbb{A}_{K,\infty}$, and $T'$, $T'_v$, $T'_\infty$ for the twisted centralizers $\{t: t\,\delta\,\sigma(t)^{-1}=\delta\}$ of $\delta$, $\delta_v$, $\delta_\infty$, with their Borel structures. Given a measure $\tau$ on $T'$, measures $\tau_v$ on $T'_v$ that are right invariant and give mass $1$ to $T'_v\cap\mathrm{Int}_v$, where $\mathrm{Int}_v\subseteq\mathrm{GL}_2(L\otimes_K K_v)$ is the set of $g$ with $g$ and $g^{-1}$ having entries in the image of $\mathcal{O}_L\otimes\mathcal{O}_v$, a finite set $S$ of finite places, and functions $\varphi$, $\varphi_\infty$, $\varphi_v$ with $\varphi(x)=\varphi_\infty(x_\infty)\prod_{v\in S}\varphi_v(x_v)$ whenever $x_v\in\mathrm{Int}_v$ for all $v\notin S$ and $\varphi(x)=0$ otherwise: assume some nonnegative, measurable, compactly supported $w$ satisfies $\int_{T'}w(tx)\,d\tau=1$ whenever $\varphi(x^{-1}\delta\sigma(x))\neq0$, and that $\varphi(x^{-1}\delta\sigma(x))\neq0$ for some $x$. Then there is a finite $S_1\supseteq S$ such that for $v\notin S_1$ the indicator of $\mathrm{Int}_v$ is such a section function at $\delta_v$ for $\tau_v$; moreover for $v\in S$ the set where $\varphi_v(y^{-1}\delta_v\sigma(y))\neq0$, for $v\notin S$ the set where $y^{-1}\delta_v\sigma(y)\in\mathrm{Int}_v$, and the set where $\varphi_\infty(y^{-1}\delta_\infty\sigma(y))\neq0$ are each contained in a product of the corresponding twisted centralizer with a compact set.
--
--   This is the first step in the Euler factorisation, over the places of the ground field, of a global twisted orbital integral of a factorizable test function: compactness of the support of a single global twisted section function yields unit local section functions at almost all places and supports that are compact modulo the local twisted centralizers. It is used in the derivation of the product formula for twisted orbital integrals of base-change type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange_of_isMulRightInvariant
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsMulRightInvariant _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) _ (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (φa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        φ x = φa (AutomorphicForm.tensorArch K L x) *
          ∏ v ∈ S, φS v (AutomorphicForm.tensorPlace K L v x))
    (hφ0 : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
        φ x = 0)
    (hw : ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ φ w)
    (hne : ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0) :
    (∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧ ∀ v ∉ S₁,
      AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ) (τf v)
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) ∧
    (∀ v ∈ S, ∃ C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          φS v (y⁻¹ * AutomorphicForm.tensorPlace K L v δ *
            AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ y) ≠ 0} ⊆
        (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ) :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * C) ∧
    (∀ v ∉ S, ∃ C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          y⁻¹ * AutomorphicForm.tensorPlace K L v δ *
              AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ y ∈
            AutomorphicForm.semiLocalIntegralSet K L v} ⊆
        (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ) :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * C) ∧
    (∃ C : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)), IsCompact C ∧
      {y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) |
          φa (y⁻¹ * AutomorphicForm.tensorArch K L δ *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ y) ≠ 0} ⊆
        (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L δ) :
          Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) * C) := by sorry
