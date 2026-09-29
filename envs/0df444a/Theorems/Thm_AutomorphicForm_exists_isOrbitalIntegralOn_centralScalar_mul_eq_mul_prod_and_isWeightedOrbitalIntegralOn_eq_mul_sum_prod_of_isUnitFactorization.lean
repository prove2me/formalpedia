-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegralOn_centralScalar_mul_eq_mul_prod_and_isWeightedOrbitalIntegralOn_eq_mul_sum_prod_of_isUnitFactorization
-- name    : AutomorphicForm.exists_isOrbitalIntegralOn_centralScalar_mul_eq_mul_prod_and_isWeightedOrbitalIntegralOn_eq_mul_sum_prod_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/ce360b99-8f84-55ec-bb8c-c9923f95f705
-- title:
--   Euler factorisation of central-translate orbital and height-weighted orbital integrals
-- statement:
--   Fix a number field $K$ and write $G=\mathrm{GL}_2$ over the various completions and adele rings of $K$; all groups carry their Borel $\sigma$-algebras (`glBorel`, `glBorelOf`, `localGLBorel`, `centralizerBorel`, `localCentralizerBorel`).
--
--   The data are: a Haar measure $\mu$ on $G(\mathbb{A}_K)$; a measure $\nu$ on $G(\mathbb{A}_{K,\infty})$ (the infinite adeles); a real constant $c_G$; an element $\gamma \in G(\mathbb{A}_K)$ with $\mathrm{tr}(\gamma)^2-4\det(\gamma)$ a unit of $\mathbb{A}_K$ (this is `IsRegularSemisimple`); a Haar measure $\tau$ on the centraliser of $\{\gamma\}$ in $G(\mathbb{A}_K)$; a Haar measure $\tau_a$ on the centraliser of the archimedean component $\gamma_\infty =$ `glArch` $\gamma$ in $G(\mathbb{A}_{K,\infty})$; for each finite place $v$ a Haar measure $\tau_v$ on the centraliser in $G(K_v)$ of the local component $\gamma_v$ of $\gamma$, normalised so that $\tau_v$ gives mass $1$ to the preimage in that centraliser of the compact open set `localIntegralSet` $K\ v$ (the $g\in G(K_v)$ with both $g$ and $g^{-1}$ having entries in $\mathcal{O}_v$); and a real constant $c_T>0$.
--
--   Two integral-factorisation hypotheses are imposed. The hypothesis `hG` states: for every finite set $S$ of finite places and every $f$ on $G(\mathbb{A}_K)$, $f_\infty$ on $G(\mathbb{A}_{K,\infty})$ and family $(f_v)_v$, if $f_\infty$ is a.e. strongly measurable for $\nu$, each $f_v$ ($v\in S$) is a.e. strongly measurable for the local Haar measure `localHaar` $K\ v$, $f(g)=f_\infty(g_\infty)\prod_{v\in S}f_v(g_v)$ whenever $g_v\in$ `localIntegralSet` $K\ v$ for all $v\notin S$, and $f(g)=0$ as soon as $g_v\notin$ `localIntegralSet` $K\ v$ for some $v\notin S$, then $\int f\,d\mu = c_G\,(\int f_\infty \,d\nu)\prod_{v\in S}\int f_v\,d(\mathrm{localHaar})$. The hypothesis `hT` states the same implication with $\mu$ replaced by $\tau$, the measures $\nu,\tau_v$ replaced by $\tau_a,\tau_v$ on the corresponding centralisers, test functions defined on the centraliser of $\gamma$, and constant $c_T$ in place of $c_G$.
--
--   The weight data consist of a real-valued function $W_\infty$ on $G(\mathbb{A}_{K,\infty})$ which is left invariant under the centraliser of $\gamma_\infty$ (`hWa`), continuous (`hWac`), and whose complexification is a.e. strongly measurable for $\nu$ (`hWam`); together with the hypothesis `hWv` that for every finite place $v$ the local weight `LocalWeight.weight` $x = 2\log\big(\max(\|x_{00}\|,\|x_{01}\|)\cdot \mathrm{rowMaxNorm}(x)/\|\det x\|\big)$ is left invariant under the centraliser of $\gamma_v$ in $G(K_v)$.
--
--   The test function data consist of a finite set $S$ of finite places and functions $f$, $f_\infty$, $f_{\mathrm{fin}}$, $(f_v)_v$ on $G(\mathbb{A}_K)$, $G(\mathbb{A}_{K,\infty})$, $G(\mathbb{A}_{K,\mathrm{fin}})$ and the $G(K_v)$, with `IsUnitFactorization` $K\ S\ f\ f_\infty\ f_{\mathrm{fin}}\ (f_v)$: $f_\infty$ is an archimedean test factor (given by a smooth function of the archimedean matrix entries, with compact support), $f_{\mathrm{fin}}$ is locally constant with compact support, each $f_v$ with $v\in S$ is locally constant with compact support, $f_{\mathrm{fin}}(h)=\prod_{v\in S}f_v(h_v)$ whenever $h_v\in$ `localIntegralSet` $K\ v$ for all $v\notin S$, $f_{\mathrm{fin}}(h)=0$ if some $h_v$ with $v\notin S$ fails to lie there, and $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$.
--
--   Finally, an idele $z\in(\mathbb{A}_K)^\times$ is fixed, with central image `centralScalar` $z$, and the hypothesis `hW` requires the global height weight to split as a sum of local weights: for every $x\in G(\mathbb{A}_K)$,
--   $$-\log H(x)-\log H(w\,x) = W_\infty(x_\infty) + \sum^{\mathrm{f}}_{v} \mathrm{weight}(x_v),$$
--   where $H$ is [`NumberField.AdelicHeight.adelicHeight`](def/NumberField_AdelicHeight.html#L158) $K$, $w=$ `adelicWeyl` is the adelic image of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and the sum is the finite (finprod-style) sum over the finite places. Two complex numbers $I$ and $J$ are given, with `hI`: $I$ is an orbital integral of $g\mapsto f(z\cdot g)$ at $\gamma$ for $(\mu,\tau)$, i.e. there exists a nonnegative measurable compactly supported section function $s$ with $\int s(tx)\,d\tau = 1$ whenever $f(z\cdot x^{-1}\gamma x)\neq 0$, and $I=\int f(z\cdot x^{-1}\gamma x)s(x)\,d\mu$; and `hJ`: $J$ is the corresponding weighted orbital integral with weight $x\mapsto -\log H(x)-\log H(wx)$, i.e. $J=\int f(z\cdot x^{-1}\gamma x)\,(-\log H(x)-\log H(wx))\,s(x)\,d\mu$ for some such section function.
--
--   The conclusion asserts the existence of a finite set $S_1$ of finite places with $S\subseteq S_1$ for which both of the following hold, where for each $v$ the translated local factor is
--   $$\phi_v(x) = \big(\text{if } v\in S \text{ then } f_v \text{ else } \mathbf{1}_{\mathrm{localIntegralSet}\,K\,v}\big)\big((\mathrm{centralScalar}\,z)_v\cdot x\big).$$
--
--   First, either $I=0$ together with one of three vanishing alternatives — that $f_\infty\big((\mathrm{centralScalar}\,z)_\infty\cdot x^{-1}\gamma_\infty x\big)=0$ for all $x\in G(\mathbb{A}_{K,\infty})$; or that there is $v\in S_1$ with $\phi_v(x^{-1}\gamma_v x)=0$ for all $x\in G(K_v)$; or that there is $v\notin S_1$ with $x^{-1}\gamma_v x\notin$ `localIntegralSet` $K\ v$ for all $x\in G(K_v)$ — or else there exist a finite set $S_2\supseteq S_1$, a complex number $I_\infty$ and a family $(I_v)_v$ of complex numbers such that $I_\infty$ is an orbital integral at $\gamma_\infty$ of $y\mapsto f_\infty((\mathrm{centralScalar}\,z)_\infty\, y)$ for $(\nu,\tau_a)$; for $v\in S_1$, $I_v$ is a local orbital integral at $\gamma_v$ of $\phi_v$ for $\tau_v$ (integration against `localHaar` $K\ v$); for $v\notin S_1$, $I_v$ is the local orbital integral at $\gamma_v$ of the indicator function of `localIntegralSet` $K\ v$; and for every finite set $T\supseteq S_2$,
--   $$I = c_G\,c_T^{-1}\,I_\infty\prod_{v\in T} I_v.$$
--
--   Second, either $J=0$ together with one of the same three vanishing alternatives (stated for $f_\infty$, for the $\phi_v$ with $v\in S_1$, and for the orbit of $\gamma_v$ at some $v\notin S_1$, exactly as above), or else there exist a finite set $S_2\supseteq S_1$, complex numbers $I_\infty, J_\infty$ and families $(I_v)_v,(J_v)_v$ such that: $I_\infty$ is an orbital integral at $\gamma_\infty$ of $y\mapsto f_\infty((\mathrm{centralScalar}\,z)_\infty\, y)$ for $(\nu,\tau_a)$; $J_\infty$ is the weighted orbital integral of the same function at $\gamma_\infty$ with weight $W_\infty$ for $(\nu,\tau_a)$; for every $v\in S_1$, $I_v$ and $J_v$ are respectively the local orbital integral and the local weighted orbital integral (with weight `LocalWeight.weight`) at $\gamma_v$ of $\phi_v$ for $\tau_v$; for every $v\notin S_1$, $I_v$ and $J_v$ are respectively the local orbital integral and the local weighted orbital integral at $\gamma_v$ of the indicator function of `localIntegralSet` $K\ v$; $J_v=0$ for all $v\notin S_2$; and for every finite set $T\supseteq S_2$,
--   $$J = c_G\,c_T^{-1}\Big(J_\infty\prod_{v\in T} I_v \; +\; I_\infty\sum_{v\in T} J_v\prod_{u\in T\setminus\{v\}} I_u\Big).$$
--   The sets $S_2$ in the two conjuncts are quantified separately, as are the archimedean and local factors occurring in them.
--
--   This is the Euler factorisation, over the adeles of $K$, of the plain orbital integral and of the height-weighted orbital integral of a central translate $f(z\,\cdot)$ of a factorisable test function on $\mathrm{GL}_2$, the weighted case producing the expected derivation (sum-over-places) shape. It is used in the analysis of the hyperbolic contributions to the trace formula comparison, being cited by the statement on weighted class integrals and archimedean windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOrbitalIntegralOn_centralScalar_mul_eq_mul_prod_and_isWeightedOrbitalIntegralOn_eq_mul_sum_prod_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem AutomorphicForm.exists_isOrbitalIntegralOn_centralScalar_mul_eq_mul_prod_and_isWeightedOrbitalIntegralOn_eq_mul_sum_prod_of_isUnitFactorization
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

    (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℝ)
    (hWa : ∀ t : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))),
      ∀ x : GL (Fin 2) (InfiniteAdeleRing K), Wa ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x) = Wa x)
    (hWac : Continuous Wa)
    (hWam : AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] (fun x => (Wa x : ℂ)) ν)
    (hWv : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ t : AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)),
      ∀ x : GL (Fin 2) (v.adicCompletion K),
        AutomorphicForm.LocalWeight.weight ((t : GL (Fin 2) (v.adicCompletion K)) * x) =
          AutomorphicForm.LocalWeight.weight x)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    [DecidableEq (HeightOneSpectrum (𝓞 K))]

    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hW : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      -Real.log (NumberField.AdelicHeight.adelicHeight K x)
          - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)) =
        Wa (AdelicLevel.glArch (𝓞 K) K x) +
          ∑ᶠ v : HeightOneSpectrum (𝓞 K),
            AutomorphicForm.LocalWeight.weight (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x)))
    (I J : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ
      (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) I)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ
      (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) =>
        -Real.log (NumberField.AdelicHeight.adelicHeight K x)
          - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
      γ τ
      (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) J) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧

    ((I = 0 ∧
      ((∀ x : GL (Fin 2) (InfiniteAdeleRing K), fa (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) *
            (x⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * x)) = 0) ∨
        (∃ v ∈ S₁, ∀ x : GL (Fin 2) (v.adicCompletion K),
          (if v ∈ S then fS v else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z)) *
              (x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x)) = 0) ∨
        (∃ v ∉ S₁, ∀ x : GL (Fin 2) (v.adicCompletion K),
          x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x ∉
            AutomorphicForm.localIntegralSet K v))) ∨
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S₂ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa
          (fun y => fa (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) * y)) Ia ∧
        (∀ v ∈ S₁, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          (fun x => (if v ∈ S then fS v else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z)) * x)) (Iv v)) ∧
        (∀ v ∉ S₁, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₂ ⊆ T →
          I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v) ∧

    ((J = 0 ∧
      ((∀ x : GL (Fin 2) (InfiniteAdeleRing K), fa (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) *
            (x⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * x)) = 0) ∨
        (∃ v ∈ S₁, ∀ x : GL (Fin 2) (v.adicCompletion K),
          (if v ∈ S then fS v else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z)) *
              (x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x)) = 0) ∨
        (∃ v ∉ S₁, ∀ x : GL (Fin 2) (v.adicCompletion K),
          x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x ∉
            AutomorphicForm.localIntegralSet K v))) ∨
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S₂ ∧
      ∃ (Ia Ja : ℂ) (Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa
          (fun y => fa (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) * y)) Ia ∧
        AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν Wa (AdelicLevel.glArch (𝓞 K) K γ) τa
          (fun y => fa (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) * y)) Ja ∧
        (∀ v ∈ S₁, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          (fun x => (if v ∈ S then fS v else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z)) * x)) (Iv v)) ∧
        (∀ v ∈ S₁, AutomorphicForm.IsWeightedOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          (fun x => (if v ∈ S then fS v else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z)) * x)) (Jv v)) ∧
        (∀ v ∉ S₁, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        (∀ v ∉ S₁, AutomorphicForm.IsWeightedOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Jv v)) ∧
        (∀ v ∉ S₂, Jv v = 0) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₂ ⊆ T →
          J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u)) := by sorry
