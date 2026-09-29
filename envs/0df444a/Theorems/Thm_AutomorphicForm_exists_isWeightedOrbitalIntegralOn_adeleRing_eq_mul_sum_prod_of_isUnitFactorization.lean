-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization
-- name    : AutomorphicForm.exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d872a6ba-8abe-5626-8d8b-3704bc867358
-- title:
--   Euler factorisation of a weighted orbital integral on GL₂
-- statement:
--   Fix a number field $K$ with ring of integers $\mathcal{O}_K$. The data are: a Haar measure $\mu$ on $GL_2(\mathbb{A}_K)$ for the Borel $\sigma$-algebra `glBorel`; a measure $\nu$ on $GL_2(K_\infty)$ for the Borel $\sigma$-algebra `glBorelOf` on the group of units over the infinite adele ring (no invariance is assumed of $\nu$); a real constant $cG$; an element $\gamma \in GL_2(\mathbb{A}_K)$ which is regular semisimple in the sense of the project predicate `IsRegularSemisimple`, namely that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $\mathbb{A}_K$; Haar measures $\tau$ on the centraliser of $\{\gamma\}$ in $GL_2(\mathbb{A}_K)$ and $\tau_a$ on the centraliser of the archimedean component $\mathrm{glArch}(\gamma)$ in $GL_2(K_\infty)$, both with their Borel structures; for each finite place $v$ a Haar measure $\tau f_v$ on the centraliser of the local component $\gamma_v = \mathrm{finComponent}_v(\mathrm{glFin}(\gamma))$ in $GL_2(K_v)$; and a real constant $cT$ with $cT > 0$.
--
--   Two groups of hypotheses express that the global measures factorise over the places. The hypothesis `hG` states: for every finite set $S$ of finite places and all functions $f$ on $GL_2(\mathbb{A}_K)$, $fa$ on $GL_2(K_\infty)$ and $fS_v$ on $GL_2(K_v)$ such that $fa$ is a.e. strongly measurable for $\nu$, each $fS_v$ with $v \in S$ is a.e. strongly measurable for the normalised local Haar measure `localHaar K v` (the Haar measure giving mass $1$ to the compact open set `localIntegralSet K v` of those $g \in GL_2(K_v)$ for which both $g$ and $g^{-1}$ have entries in the valuation ring $\mathcal{O}_v$), such that $f(g) = fa(\mathrm{glArch}(g))\prod_{v \in S} fS_v(g_v)$ whenever all components $g_v$ with $v \notin S$ lie in `localIntegralSet K v`, and $f(g) = 0$ as soon as some component $g_v$ with $v \notin S$ fails to lie there, one has
--   $$\int f \, d\mu = cG \cdot \Big(\int fa \, d\nu\Big) \cdot \prod_{v \in S} \int fS_v \, d(\mathrm{localHaar}\,K\,v).$$
--   The hypothesis `hT` is the exactly parallel statement for the centraliser of $\gamma$: for every finite $S$ and all $W$ on the centraliser of $\{\gamma\}$, $Wa$ on $GL_2(K_\infty)$ and $WS_v$ on $GL_2(K_v)$, subject to a.e. strong measurability of $Wa$ for $\tau_a$ and of each $WS_v$ ($v \in S$) for $\tau f_v$, the product formula $W(t) = Wa(\mathrm{glArch}(t))\prod_{v\in S} WS_v(t_v)$ for those $t$ whose components off $S$ lie in the local integral sets, and vanishing of $W(t)$ when some component off $S$ does not, one has $\int W \, d\tau = cT \cdot (\int Wa \, d\tau_a) \cdot \prod_{v \in S} \int WS_v \, d(\tau f_v)$. In addition the local centraliser measures are normalised by `hτf1`: for every finite place $v$, $\tau f_v$ gives mass $1$ to the preimage of `localIntegralSet K v` under the inclusion of the centraliser.
--
--   The weight data are: a real-valued function $Wa$ on $GL_2(K_\infty)$ which is left invariant under the centraliser of $\mathrm{glArch}(\gamma)$ (`hWa`), continuous (`hWac`), and whose complexification is a.e. strongly measurable for $\nu$ (`hWam`); and the hypothesis `hWv` that for every finite place $v$ the local weight $\mathrm{weight}(x) = 2\log\big(\max(\lVert x_{00}\rVert, \lVert x_{01}\rVert)\cdot\max(\lVert x_{10}\rVert, \lVert x_{11}\rVert)/\lVert\det x\rVert\big)$ is left invariant under the centraliser of $\gamma_v$ in $GL_2(K_v)$.
--
--   The test function data are a finite set $S$ of finite places and functions $f$ on $GL_2(\mathbb{A}_K)$, $fa$ on $GL_2(K_\infty)$, $ff$ on $GL_2(\mathbb{A}_{K,\mathrm{fin}})$ and $fS_v$ on $GL_2(K_v)$ satisfying `IsUnitFactorization K S f fa ff fS`, which asserts: $fa$ is an archimedean test factor (its matrix entries are read off into the mixed space, where $fa$ is given by a $C^\infty$ function, and $fa$ has compact support); $ff$ is locally constant with compact support; each $fS_v$ with $v \in S$ is locally constant with compact support; $ff(h) = \prod_{v \in S} fS_v(h_v)$ whenever all components $h_v$ with $v \notin S$ lie in `localIntegralSet K v`; $ff(h) = 0$ when some component off $S$ does not; and $f(g) = fa(\mathrm{glArch}(g))\, ff(\mathrm{glFin}(g))$ for all $g$.
--
--   Finally, $J \in \mathbb{C}$ is assumed, via `hJ`, to be a weighted orbital integral of $f$ at $\gamma$ on $GL_2(\mathbb{A}_K)$ with respect to $\mu$, $\tau$ and the global weight $x \mapsto Wa(\mathrm{glArch}(x)) + \sum^{\mathrm{f}}_{v} \mathrm{weight}(x_v)$ (the finite-support sum $\sum^{\mathrm{f}}$ over all finite places); that is, there exists a section function $s$ — non-negative, measurable, of compact support, and with $\int_{Z} s(t x)\, d\tau = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$, $Z$ the centraliser of $\{\gamma\}$ — such that $J = \int f(x^{-1}\gamma x)\,\big(Wa(\mathrm{glArch}(x)) + \sum^{\mathrm{f}}_v \mathrm{weight}(x_v)\big)\, s(x)\, d\mu$.
--
--   The conclusion is a disjunction of two alternatives.
--
--   The first alternative is that $J = 0$ and at least one of the following local vanishing statements holds: $fa$ vanishes on the whole conjugacy orbit of $\mathrm{glArch}(\gamma)$, i.e. $fa(x^{-1}\mathrm{glArch}(\gamma)x) = 0$ for all $x \in GL_2(K_\infty)$; or there is $v \in S$ with $fS_v(x^{-1}\gamma_v x) = 0$ for all $x \in GL_2(K_v)$; or there is $v \notin S$ such that no conjugate $x^{-1}\gamma_v x$ lies in `localIntegralSet K v`.
--
--   The second alternative asserts the existence of a finite set $S_1$ of finite places with $S \subseteq S_1$, of complex numbers $Ia$, $Ja$ and of families $Iv, Jv$ indexed by the finite places such that: $Ia$ is an orbital integral of $fa$ at $\mathrm{glArch}(\gamma)$ with respect to $\nu$ and $\tau_a$; $Ja$ is a $Wa$-weighted orbital integral of $fa$ at $\mathrm{glArch}(\gamma)$ with respect to $\nu$ and $\tau_a$; for every $v \in S$, $Iv_v$ is a local orbital integral of $fS_v$ at $\gamma_v$ with respect to `localHaar K v` and $\tau f_v$, and $Jv_v$ is the corresponding orbital integral weighted by $\mathrm{weight}$; for every $v \notin S$, $Iv_v$ and $Jv_v$ are respectively the local orbital integral and the $\mathrm{weight}$-weighted local orbital integral, at $\gamma_v$ and with respect to $\tau f_v$, of the indicator function of `localIntegralSet K v` with value $1 \in \mathbb{C}$; $Jv_v = 0$ for every $v \notin S_1$; and for every finite set $T$ of finite places with $S_1 \subseteq T$,
--   $$J = cG \cdot cT^{-1}\Big(Ja \prod_{v \in T} Iv_v + Ia \sum_{v \in T} Jv_v \prod_{u \in T \setminus \{v\}} Iv_u\Big).$$
--   Here each assertion of the form "$X$ is a (weighted) orbital integral" has the meaning unfolded above: existence of a non-negative, measurable, compactly supported section function whose integral over the relevant centraliser equals $1$ at every point where the conjugated test function is non-zero, together with the corresponding integral formula for $X$.
--
--   This is the Euler factorisation, with a Leibniz term over the places, of a height-weighted orbital integral of a factorisable test function at a regular semisimple element of $GL_2(\mathbb{A}_K)$: the global weighted integral is expressed through one archimedean and countably many local (weighted) orbital integrals, almost all of which are those of the indicator of the local integral set. It is the weighted half of the factorisation of orbital integrals on the $K$-side, and is combined with the unweighted factorisation in the companion statement about translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization.lean

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

theorem AutomorphicForm.exists_isWeightedOrbitalIntegralOn_adeleRing_eq_mul_sum_prod_of_isUnitFactorization
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
    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ
      (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) => Wa (AdelicLevel.glArch (𝓞 K) K x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K),
          AutomorphicForm.LocalWeight.weight (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x)))
      γ τ f J) :
    (J = 0 ∧
      ((∀ x : GL (Fin 2) (InfiniteAdeleRing K), fa (x⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * x) = 0) ∨
        (∃ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K),
          fS v (x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x) = 0) ∨
        (∃ v ∉ S, ∀ x : GL (Fin 2) (v.adicCompletion K),
          x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x ∉
            AutomorphicForm.localIntegralSet K v))) ∨
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia Ja : ℂ) (Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa fa Ia ∧
        AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν Wa (AdelicLevel.glArch (𝓞 K) K γ) τa fa Ja ∧
        (∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (Iv v)) ∧
        (∀ v ∈ S, AutomorphicForm.IsWeightedOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (Jv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsWeightedOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Jv v)) ∧
        (∀ v ∉ S₁, Jv v = 0) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u) := by sorry
