-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
-- name    : AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/0b32b4ec-b580-546f-b971-709212cc3a96
-- title:
--   Semi-local twisted section data for a factorisable function
-- statement:
--   Let $K \subseteq L$ be number fields and $\sigma$ a $K$-automorphism of $L$ with $\sigma^{[L:K]} = 1$; for a $K$-algebra $A$ let $\sigma$ act on $GL_2(L \otimes_K A)$ through the left factor, write $\sigma$ again for this action, and write $\delta_v$, $\delta_\infty$ for the images of $\delta \in GL_2(L \otimes_K \mathbb{A}_K)$ under the maps induced by $L \otimes_K \mathbb{A}_K \to L \otimes_K K_v$ and $L \otimes_K \mathbb{A}_K \to L \otimes_K K_\infty$. Assume the norm string $\delta \,\sigma(\delta) \cdots \sigma^{[L:K]-1}(\delta)$ has $\operatorname{tr}^2 - 4\det$ a unit. Let $\tau$ be a measure on the twisted centraliser $T' = \{t : t\delta\sigma(t)^{-1} = \delta\}$ (Borel structure from the subspace topology), and for each finite place $v$ of $K$ let $\tau_v$ be a left-invariant measure on $T'_v = \{t : t\delta_v\sigma(t)^{-1} = \delta_v\}$ giving mass $1$ to the points of $T'_v$ lying in the semi-local integral set $\Omega_v$, the set of $g \in GL_2(L \otimes_K K_v)$ such that $g$ and $g^{-1}$ have entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$. Let $S$ be a finite set of finite places and let $\varphi$ on $GL_2(L \otimes_K \mathbb{A}_K)$, $\varphi_\infty$ on $GL_2(L \otimes_K K_\infty)$ and $\varphi_v$ on $GL_2(L \otimes_K K_v)$ be complex-valued with $\varphi(x) = \varphi_\infty(x_\infty) \prod_{v \in S} \varphi_v(x_v)$ whenever $x_v \in \Omega_v$ for all $v \notin S$, and $\varphi(x) = 0$ as soon as $x_v \notin \Omega_v$ for some $v \notin S$. Assume there exists $w \ge 0$, measurable with compact support, such that $\int_{T'} w(tx)\, d\tau = 1$ for every $x$ with $\varphi(x^{-1}\delta\sigma(x)) \ne 0$, and that some $x$ indeed has $\varphi(x^{-1}\delta\sigma(x)) \ne 0$. Then: (i) there is a finite set $S_1 \supseteq S$ of finite places such that for every $v \notin S_1$ the indicator function of $\Omega_v$ is a twisted section function at $\delta_v$ for $\tau_v$, i.e. it is non-negative, measurable, of compact support, and $\int_{T'_v} \mathbf{1}_{\Omega_v}(ty)\, d\tau_v = 1$ for every $y$ with $y^{-1}\delta_v\sigma(y) \in \Omega_v$; (ii) for $v \in S$ the set where $y \mapsto \varphi_v(y^{-1}\delta_v\sigma(y))$ is non-zero is contained in $T'_v \cdot C$ for some compact $C$; (iii) for $v \notin S$ the set of $y$ with $y^{-1}\delta_v\sigma(y) \in \Omega_v$ is contained in $T'_v \cdot C$ for some compact $C$; and (iv) the set where $y \mapsto \varphi_\infty(y^{-1}\delta_\infty\sigma(y))$ is non-zero is contained in $T'_\infty \cdot C$ for some compact $C$, where $T'_\infty$ is the twisted centraliser of $\delta_\infty$.
--
--   This provides the local input for the Euler factorisation of twisted orbital integrals in the base-change setting: part (i) identifies almost all local factors as the unit ones, while parts (ii)–(iv) record that at each place the twisted orbit map has support compact modulo the local twisted centraliser, which is what permits local twisted section functions to be built at the remaining finitely many places. It is used in the factorisation of twisted orbital integrals and of their weighted variants for a semi-locally factorisable function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsMulLeftInvariant _
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
