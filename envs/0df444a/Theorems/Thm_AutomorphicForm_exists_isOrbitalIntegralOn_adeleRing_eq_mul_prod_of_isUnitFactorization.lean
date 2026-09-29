-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
-- name    : AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c89b7eb7-c515-595e-b41f-0875ba79d275
-- title:
--   Factorisation of adelic orbital integrals of unit-factorizable functions
-- statement:
--   Let $K$ be a number field, $\mu$ a Haar measure for the Borel structure on $GL_2(\mathbb{A}_K)$, and $\nu$ a measure (no invariance assumed) on $GL_2(K_\infty)$. Assume a real constant $c_G$ for which, for every finite set $S$ of finite places and all $f$ on $GL_2(\mathbb{A}_K)$, $f_\infty$ on $GL_2(K_\infty)$ and $f_v$ on $GL_2(K_v)$ with $f_\infty$ a.e. strongly measurable for $\nu$ and $f_v$ for [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) ($v\in S$), such that $f(g)=f_\infty(g_\infty)\prod_{v\in S}f_v(g_v)$ whenever $g_v\in$ `localIntegralSet K v` for all $v\notin S$ and $f(g)=0$ when some such $g_v$ fails this, one has $\int f\,d\mu=c_G(\int f_\infty\,d\nu)\prod_{v\in S}\int f_v\,d(\mathrm{localHaar}\,K\,v)$. Let $\gamma\in GL_2(\mathbb{A}_K)$ satisfy `IsRegularSemisimple`, i.e. $\operatorname{tr}(\gamma)^2-4\det\gamma$ is a unit of $\mathbb{A}_K$; let $\tau$, $\tau_\infty$ and $\tau_v$ be Haar measures on the centralizers of $\gamma$, of $\gamma_\infty$ and of each $\gamma_v$, with $\tau_v$ giving mass $1$ to the part of `localIntegralSet K v` in the centralizer, and assume the analogous product formula for these measures with a constant $c_T>0$. Let $S$ be a finite set of finite places and $(f,f_\infty,f_{\mathrm{fin}},(f_v))$ satisfy `IsUnitFactorization`: $f_\infty$ is an archimedean test factor (a compactly supported function given by a smooth function of the matrix entries in the mixed space), $f_{\mathrm{fin}}$ satisfies `IsFinTestFactor`, each $f_v$ for $v\in S$ satisfies `IsLocalTestFn`, $f_{\mathrm{fin}}(h)=\prod_{v\in S}f_v(h_v)$ when $h_v\in$ `localIntegralSet K v` for all $v\notin S$ and $f_{\mathrm{fin}}(h)=0$ otherwise, and $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$. Finally let $I$ be an orbital integral of $f$ at $\gamma$ for $\mu,\tau$, meaning $I=\int f(x^{-1}\gamma x)w(x)\,d\mu$ for some $w$ with `IsSectionFnOn`. The conclusion is a disjunction. Either $I=0$ and one of the following holds: $f_\infty$ vanishes on the whole conjugacy class of $\gamma_\infty$; or for some $v\in S$, $f_v$ vanishes on the conjugacy class of $\gamma_v$; or for some $v\notin S$ no conjugate of $\gamma_v$ lies in `localIntegralSet K v`. Or else there are a finite set $S_1\supseteq S$, a number $I_\infty$ and numbers $I_v$ such that $I_\infty$ is an orbital integral of $f_\infty$ at $\gamma_\infty$ for $\nu,\tau_\infty$, $I_v$ is the local orbital integral (in the sense of [`AutomorphicForm.IsOrbitalIntegral`](def/AutomorphicForm_LocalOrbitalBase.html#L208), with respect to $\tau_v$ and `localHaar K v`) of $f_v$ at $\gamma_v$ for $v\in S$ and of the indicator function of `localIntegralSet K v` at $\gamma_v$ for $v\notin S$, and $I=c_Gc_T^{-1}I_\infty\prod_{v\in T}I_v$ for every finite set $T\supseteq S_1$.
--
--   This is the Euler factorisation of a global orbital integral on $GL_2$ over a number field: the orbital integral of a function with a unit factorization splits as a constant times the archimedean orbital integral times the product of the local orbital integrals, almost all of which are unit orbital integrals, the product being independent of the finite set over which it is taken beyond a suitable $S_1$. It is used in the statements comparing global orbital integrals of matching test functions, in particular in the results establishing matching at the adelic level from matching place by place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
    (K : Type) [Field K] [NumberField K]
    (μ : @Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) (glBorel (Fin 2) (𝓞 K) K))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 K) K)) _ _ (glBorel (Fin 2) (𝓞 K) K) μ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μ = cG * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ) τ)
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K γ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))] (fun t => WS v t) (τf v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ f I) :
    (I = 0 ∧
      ((∀ x : GL (Fin 2) (InfiniteAdeleRing K), fa (x⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * x) = 0) ∨
        (∃ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K),
          fS v (x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x) = 0) ∨
        (∃ v ∉ S, ∀ x : GL (Fin 2) (v.adicCompletion K),
          x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x ∉
            AutomorphicForm.localIntegralSet K v))) ∨
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa
          fa Ia ∧
        (∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by sorry
