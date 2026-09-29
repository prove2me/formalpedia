-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
-- name    : AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/733c351b-1b01-57e2-b7e3-8914571fd0a5
-- title:
--   Euler factorisation of a global twisted orbital integral
-- statement:
--   Let $L/K$ be an extension of number fields of degree $n=[L:K]$ and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma^{n}=1$, acting on $\mathrm{GL}_2(L\otimes_K A)$ through the first tensor factor (`sigmaGL`). Fix: a Haar measure $\mu$ on $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ for the Borel structure `glBorelOf`; a measure $\nu$ on $\mathrm{GL}_2(L\otimes_K K_\infty)$; a real constant $c_G$ such that, for every finite set $S$ of finite places of $K$ and all $F$, $F_\infty$, $(F_v)_v$ with $F_\infty$ a.e. strongly measurable for $\nu$ and $F_v$ for the measure `semiLocalHaar` at $v\in S$, satisfying $F(x)=F_\infty(x_\infty)\prod_{v\in S}F_v(x_v)$ whenever $x_v$ lies in the integral set `semiLocalIntegralSet` for all $v\notin S$ and $F(x)=0$ when some $x_v$, $v\notin S$, fails to, one has $\int F\,d\mu=c_G(\int F_\infty\,d\nu)\prod_{v\in S}\int F_v\,d(\mathrm{semiLocalHaar})$; an element $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ whose norm string $\delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$ is regular semisimple, i.e. $\mathrm{tr}^2-4\det$ is a unit; Haar measures $\tau$, $\tau_\infty$, $\tau_v$ on the twisted centralisers (`sigmaCentralizer`) of $\delta$, of its archimedean image and of its images $\delta_v$, with $\tau_v$ normalised to give the preimage of `semiLocalIntegralSet` mass $1$; a constant $c_T>0$ and the analogous factorisation hypothesis for integrals over the twisted centraliser. Fix further a finite set $S$ of finite places, functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $\varphi_\infty$ on $\mathrm{GL}_2(L_\infty)$, $\varphi_f$ on $\mathrm{GL}_2(\mathbb{A}_{L,f})$ and $\varphi_v$ on $\mathrm{GL}_2(L\otimes_K K_v)$ forming a semi-local factorisation in the sense of `IsSemiLocalFactorization` ($\varphi_\infty$ an archimedean test factor, $\varphi_f$ a finite test factor, $\varphi_v$ semi-local test functions for $v\in S$, $\varphi_f(h)=\prod_{v\in S}\varphi_v(h_v)$ for $h$ integral outside $S$ and $\varphi_f(h)=0$ otherwise, and $\varphi=\varphi_\infty\cdot\varphi_f$ on archimedean and finite components); and $I\in\mathbb{C}$ such that $I$ is a twisted orbital integral of $\varphi\circ$`baseChangeGL` at $\delta$ for $\mu$ and $\tau$, i.e. $I=\int\varphi(x^{-1}\delta\,\sigma(x))w(x)\,d\mu$ for some twisted section function $w$ for $\tau$. Then either $I=0$ and one of the following vanishing alternatives holds: $\varphi_\infty\circ$`archIdentGL` vanishes identically on the twisted orbit $x^{-1}\delta_\infty\sigma(x)$; or some $v\in S$ has $\varphi_v$ vanishing identically on the twisted orbit of $\delta_v$; or some $v\notin S$ has the whole twisted orbit of $\delta_v$ disjoint from `semiLocalIntegralSet`; or else there are a finite set $S_1\supseteq S$ of finite places, a number $I_\infty$ which is a twisted orbital integral of $\varphi_\infty\circ$`archIdentGL` at the archimedean image of $\delta$ for $\nu$ and $\tau_\infty$, and numbers $I_v$ which are local twisted orbital integrals at $\delta_v$ for `semiLocalHaar` and $\tau_v$, of $\varphi_v$ for $v\in S$ and of the indicator function of `semiLocalIntegralSet` for $v\notin S$, such that $I=c_G\,c_T^{-1}\,I_\infty\prod_{v\in T}I_v$ for every finite set $T\supseteq S_1$.
--
--   This is the twisted analogue, taken over the places of the ground field $K$, of the factorisation of a global orbital integral into an archimedean factor and local factors which are $1$ outside a finite set. It is used in the comparison of orbital integrals on $\mathrm{GL}_2(\mathbb{A}_L)$ with twisted ones for base change, and is cited by the results producing matching functions over the adele ring and the bounds on orbital integrals over double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ x, F x ∂μ = cG * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
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
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (I : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
      (φ ∘ AutomorphicForm.baseChangeGL K L) I) :
    (I = 0 ∧
      ((∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
          φa (AutomorphicForm.archIdentGL K L (x⁻¹ * AutomorphicForm.tensorArch K L δ *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) = 0) ∨
        (∃ v ∈ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          φS v (x⁻¹ * AutomorphicForm.tensorPlace K L v δ *
            AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) = 0) ∨
        (∃ v ∉ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          x⁻¹ * AutomorphicForm.tensorPlace K L v δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∉
            AutomorphicForm.semiLocalIntegralSet K L v))) ∨
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν
          (AutomorphicForm.tensorArch K L δ) τa (φa ∘ AutomorphicForm.archIdentGL K L) Ia ∧
        (∀ v ∈ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v)
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by sorry
