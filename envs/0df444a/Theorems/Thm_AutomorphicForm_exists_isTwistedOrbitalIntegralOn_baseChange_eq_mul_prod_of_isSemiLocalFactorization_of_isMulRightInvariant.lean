-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
-- name    : AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6fed7fc3-1ac4-5022-be9c-06453d81529d
-- title:
--   Euler factorisation of twisted orbital integrals over places of K
-- statement:
--   Let $L/K$ be an extension of number fields and $\sigma$ a $K$-algebra automorphism of $L$, acting on $GL_2(L\otimes_K A)$ through the first tensor factor (`sigmaGL`). Let $\mu$ be a Haar measure for the Borel structure on $GL_2(L\otimes_K\mathbb{A}_K)$, let $\nu$ be a measure on $GL_2(L\otimes_K K_\infty)$, and let $c_G\in\mathbb{R}$ be such that for every finite set $S$ of finite places of $K$ and every function $F$ on the adelic group which, on the locus where all components outside $S$ lie in `semiLocalIntegralSet` $=$ the integral units of $\mathcal{O}_L\otimes\mathcal{O}_v$, equals $F_\infty(\mathrm{tensorArch}\,x)\prod_{v\in S}F_v(\mathrm{tensorPlace}_v x)$ and vanishes elsewhere (the factors being almost everywhere strongly measurable for $\nu$ and for the normalised semi-local Haar measures), one has $\int F\,d\mu=c_G(\int F_\infty\,d\nu)\prod_{v\in S}\int F_v\,d(\mathrm{semiLocalHaar})$. Let $\delta\in GL_2(L\otimes_K\mathbb{A}_K)$ be arbitrary, let $\tau$ be a Haar measure on the $\sigma$-twisted centraliser of $\delta$ which is moreover right invariant, and let $\tau_\infty$, $\tau_v$ be Haar measures on the twisted centralisers of $\mathrm{tensorArch}\,\delta$ and of $\mathrm{tensorPlace}_v\,\delta$, with $\tau_v$ giving mass $1$ to the preimage of `semiLocalIntegralSet`; assume a constant $c_T>0$ for which the analogous factorisation of $\int\,d\tau$ over $\tau_\infty$ and the $\tau_v$ holds. Let $S$ be a finite set of finite places of $K$ and let $\varphi$ on $GL_2(\mathbb{A}_L)$, $\varphi_\infty$, $\varphi_f$, $(\varphi_v)_v$ satisfy `IsSemiLocalFactorization`: $\varphi_\infty$ is an archimedean test factor, $\varphi_f$ a finite test factor, each $\varphi_v$ ($v\in S$) a semi-local test function, $\varphi_f(h)=\prod_{v\in S}\varphi_v(h_v)$ whenever all semi-local components of $h$ outside $S$ are integral and $\varphi_f(h)=0$ otherwise, and $\varphi(g)=\varphi_\infty(g_\infty)\varphi_f(g_f)$. Finally let $I\in\mathbb{C}$ be a twisted orbital integral of $\varphi\circ\mathrm{baseChangeGL}$ at $\delta$ for $\mu$ and $\tau$, that is $I=\int\varphi(\mathrm{baseChange}(x^{-1}\delta\,\sigma(x)))w(x)\,d\mu$ for some twisted section weight $w$ adapted to $\tau$. The conclusion is a disjunction. Either $I=0$ together with one of: $\varphi_\infty(\mathrm{archIdentGL}(x^{-1}(\mathrm{tensorArch}\,\delta)\sigma(x)))=0$ for all $x$; or some $v\in S$ with $\varphi_v$ vanishing along the whole twisted orbit of $\mathrm{tensorPlace}_v\,\delta$; or some $v\notin S$ whose twisted orbit of $\mathrm{tensorPlace}_v\,\delta$ meets `semiLocalIntegralSet` nowhere. Or else there are a finite set $S_1\supseteq S$, a number $I_\infty$ which is a twisted orbital integral of $\varphi_\infty\circ\mathrm{archIdentGL}$ at $\mathrm{tensorArch}\,\delta$ for $\nu$ and $\tau_\infty$, and numbers $I_v$ which are the local twisted orbital integrals at $\mathrm{tensorPlace}_v\,\delta$ for $\tau_v$ of $\varphi_v$ for $v\in S$ and of the indicator of `semiLocalIntegralSet` for $v\notin S$, such that $I=c_G c_T^{-1}I_\infty\prod_{v\in T}I_v$ for every finite set $T\supseteq S_1$.
--
--   This is the factorisation of a global twisted orbital integral into an archimedean factor and an Euler product over the finite places of the ground field $K$, for a semi-locally factorisable test function and at an arbitrary class whose twisted centraliser is unimodular; the degenerate branch records the cases in which the global integral vanishes because some local twisted orbit is missed. It is used in the comparison of twisted orbital integrals with ordinary orbital integrals at classes of central norm, where the twisted centraliser is the adelic points of $GL_2$ or of a quaternion algebra over $K$ and is unimodular but not commutative.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
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
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (hτr : @Measure.IsMulRightInvariant _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) _ τ)
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
