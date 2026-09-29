-- Prove2me | Theorems.Thm_AutomorphicForm_mul_prod_eq_zero_of_forall_apply_conj_eq_zero_of_isUnitFactorization
-- name    : AutomorphicForm.mul_prod_eq_zero_of_forall_apply_conj_eq_zero_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/1662966a-4ad2-5906-8561-35bccc624002
-- title:
--   Orbit vanishing forces a product of local orbital integrals to vanish
-- statement:
--   Let $K$ be a number field. Given: a Haar measure $\mu$ on $\mathrm{GL}_2(\mathbb{A}_K)$ for the Borel $\sigma$-algebra `glBorel`; a measure $\nu$ on $\mathrm{GL}_2$ of the infinite adeles for its Borel $\sigma$-algebra; a real constant $cG$ and the hypothesis `hG` that for every finite set $S$ of finite places and every triple of functions $f$, $fa$, $fS$ with $fa$ a.e. strongly measurable for $\nu$ and each $fS_v$ ($v\in S$) a.e. strongly measurable for the local Haar measure `localHaar`, if $f(g)=fa(g_\infty)\prod_{v\in S} fS_v(g_v)$ whenever all components of $g$ outside $S$ lie in `localIntegralSet K v` (the integral units set of $\mathcal O_v$ in $\mathrm{GL}_2$) and $f(g)=0$ whenever some component outside $S$ fails to lie there, then $\int f\,d\mu = cG\,(\int fa\,d\nu)\prod_{v\in S}\int fS_v\,d(\mathtt{localHaar})$; an element $\gamma\in\mathrm{GL}_2(\mathbb{A}_K)$ with $\operatorname{tr}(\gamma)^2-4\det(\gamma)$ a unit of $\mathbb{A}_K$; Haar measures $\tau$, $\tau a$, $\tau f_v$ on the centralizers of $\gamma$, of $\gamma_\infty$ and of each $\gamma_v$, with $\tau f_v$ of the preimage of `localIntegralSet K v` equal to $1$; a constant $cT>0$ and the hypothesis `hT` expressing the same factorisation of integrals over the centralizer of $\gamma$ into $\tau a$ and the $\tau f_v$. Let $S$ be a finite set of finite places and $f$, $fa$, $ff$, $fS$ functions on $\mathrm{GL}_2$ of the adeles, of the infinite adeles, of the finite adeles, and of each completion, satisfying `IsUnitFactorization K S f fa ff fS`: $fa$ is smooth with compact support as a function of the mixed-space entries, $ff$ satisfies `IsFinTestFactor`, each $fS_v$ ($v\in S$) satisfies `IsLocalTestFn`, $ff(h)=\prod_{v\in S} fS_v(h_v)$ for $h$ integral outside $S$, $ff(h)=0$ if some component outside $S$ is not integral, and $f(g)=fa(g_\infty)\,ff(g_{\mathrm{fin}})$. Assume $\gamma$ is integral outside $S$, and $f(x^{-1}\gamma x)=0$ for all $x\in\mathrm{GL}_2(\mathbb{A}_K)$. Let $Ia$ be an orbital integral of $fa$ at $\gamma_\infty$ relative to $\nu$ and $\tau a$, that is $Ia=\int fa(x^{-1}\gamma_\infty x)\,w(x)\,d\nu$ for some real weight $w$ satisfying `IsSectionFnOn`, and for each $v\in S$ let $Iv_v$ be likewise an orbital integral of $fS_v$ at $\gamma_v$ relative to `localHaar K v` and $\tau f_v$. Then $Ia\cdot\prod_{v\in S} Iv_v=0$.
--
--   This is the local–global step saying that a unit-factorizable test function vanishing on the entire conjugacy class of a regular semisimple $\gamma$ which is integral outside $S$ has a vanishing product of local orbital integrals, the places outside $S$ contributing factors $1$. It is used in the packaging of class sums, being cited by [`AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero`](thm.html#AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mul_prod_eq_zero_of_forall_apply_conj_eq_zero_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem AutomorphicForm.mul_prod_eq_zero_of_forall_apply_conj_eq_zero_of_isUnitFactorization
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
    (hint : ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) ∈
      AutomorphicForm.localIntegralSet K v)
    (hvan : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f (x⁻¹ * γ * x) = 0)
    (Ia : ℂ)
    (hIa : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa fa Ia)
    (Iv : HeightOneSpectrum (𝓞 K) → ℂ)
    (hIv : ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (Iv v)) :
    Ia * ∏ v ∈ S, Iv v = 0 := by sorry
