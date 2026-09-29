-- Prove2me | Theorems.Thm_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
-- name    : AutomorphicForm.isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/966dfb8a-025b-5f59-8f20-05368519c926
-- title:
--   Products of local twisted section functions are global
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-automorphism of $L$, acting on $\mathrm{GL}_2(L \otimes_K A)$ through the first tensor factor, and let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, with images $\delta_\infty$ under [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46) (base change along $\mathbb{A}_K \to K_\infty$) and $\delta_v$ under [`AutomorphicForm.tensorPlace`](def/AutomorphicForm_BaseChangePlaces.html#L49) at each $v$ in the height-one spectrum of $\mathcal{O}_K$. On the twisted centralizers $\{t : t\delta\sigma(t)^{-1} = \delta\}$ of $\delta$, $\delta_\infty$ and each $\delta_v$, equipped with their Borel structures, fix measures $\tau$, $\tau_a$, $\tau_f(v)$, and fix $c > 0$ satisfying the following factorisation hypothesis $h\tau$: for every finite set $S$ of finite places and all functions $W$, $W_\infty$, $W_v$ with values in $\mathbb{C}$ on the global, archimedean and $v$-adic groups, such that $W_\infty$ is a.e. strongly measurable on the archimedean twisted centralizer and each $W_v$ ($v \in S$) on the $v$-adic one, such that $W(t) = W_\infty(t_\infty)\prod_{v \in S} W_v(t_v)$ for all $t$ in the global twisted centralizer whose components $t_v$ lie in [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136) at every $v \notin S$ (the $g$ with $g$ and $g^{-1}$ having entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$), and $W(t) = 0$ for all other such $t$, one has $\int W \,d\tau = c \cdot (\int W_\infty \,d\tau_a) \cdot \prod_{v \in S} \int W_v \,d\tau_f(v)$. Let further $S$ be a finite set of finite places and $\varphi$, $\varphi_\infty$, $\varphi_v$ complex functions on the global, archimedean and $v$-adic groups with $\varphi(x) = \varphi_\infty(x_\infty)\prod_{v\in S}\varphi_v(x_v)$ whenever $x_v$ is semi-local integral for all $v \notin S$, and $\varphi(x) = 0$ otherwise. Assume $w_\infty$ is a twisted section function for $(\delta_\infty, \tau_a, \varphi_\infty)$, that $w_v$ is one for $(\delta_v, \tau_f(v), \varphi_v)$ for each $v \in S$, and that for $v \notin S$ the real indicator of the semi-local integral set is one for $(\delta_v, \tau_f(v))$ and the complex indicator of that set; here being a twisted section function means: non-negative, Borel measurable, compactly supported, and $\int w(tx)\,d\tau' = 1$ over the relevant twisted centralizer for every $x$ with $\varphi(x^{-1}\delta\sigma(x)) \neq 0$. The conclusion is that the function sending $x$ to $c^{-1}\,w_\infty(x_\infty)\prod_{v\in S} w_v(x_v)$ on the set of $x$ whose components are semi-local integral at all $v \notin S$, and to $0$ elsewhere, is a twisted section function for $\delta$, $\tau$ and $\varphi$.
--
--   This is the twisted, base-changed analogue of the statement that a product of local section functions is a global section function: it supplies the section function needed to write a global twisted orbital integral of a factorizable test function on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ as a product of local twisted orbital integrals. It is used by the results expressing twisted, and twisted weighted, orbital integrals over a semi-local factorisation as a constant times a product (respectively a sum of products) of local integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (c : ℝ) (hc : 0 < c)
    (hτ : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
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
    (wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (hwa : AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ) τa φa wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ)
    (hwf : ∀ v ∈ S, AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (wf v))
    (hunit : ∀ v ∉ S, AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ) (τf v)
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) :
    AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ φ
      ({x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          ∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v}.indicator
        fun x => c⁻¹ * (wa (AutomorphicForm.tensorArch K L x) *
          ∏ v ∈ S, wf v (AutomorphicForm.tensorPlace K L v x))) := by sorry
