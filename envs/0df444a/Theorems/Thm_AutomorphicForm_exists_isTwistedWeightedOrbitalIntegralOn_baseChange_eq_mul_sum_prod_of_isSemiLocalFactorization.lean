-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
-- name    : AutomorphicForm.exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/a272043d-f077-5882-9b0d-518307e69c6b
-- title:
--   Leibniz expansion of a twisted weighted orbital integral
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ satisfy $\sigma^{[L:K]} = 1$ (`hσ`). Throughout, the groups $\mathrm{GL}_2$ of the rings $L \otimes_K \mathbb{A}_K$, $L \otimes_K \mathbb{A}_{K,\infty}$ and $L \otimes_K K_v$ (for $v$ in the height-one spectrum of $\mathcal{O}_K$) carry the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), and [`AutomorphicForm.tensorArch`](def/AutomorphicForm_BaseChangePlaces.html#L46) and [`AutomorphicForm.tensorPlace K L v`](def/AutomorphicForm_BaseChangePlaces.html#L49) denote the group homomorphisms induced by $\mathrm{id}_L \otimes$ (projection of $\mathbb{A}_K$ to $\mathbb{A}_{K,\infty}$, resp. to $K_v$). For a $K$-algebra $A$, [`AutomorphicForm.sigmaGL K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L202) is the automorphism of $\mathrm{GL}_2(L \otimes_K A)$ induced by $\sigma \otimes \mathrm{id}_A$, and [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) is the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ such that both $g$ and $g^{-1}$ have all entries in the image of the semi-local integers $\mathcal{O}_L \otimes$-completion map, [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) being the Haar measure normalised to give this set mass one.
--
--   The data are: a Haar measure $\mu$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ (`hμ`); a measure $\nu$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, for which no invariance is assumed; and a real constant $c_G$ together with the hypothesis `hG` that $\mu$ factorises with constant $c_G$: for every finite set $S'$ of finite places of $K$ and all functions $F$, $F_a$, $F_{S'}(v)$ on the global, archimedean and semi-local groups with values in $\mathbb{C}$ such that $F_a$ is almost everywhere strongly $\nu$-measurable, each $F_{S'}(v)$ ($v \in S'$) is almost everywhere strongly measurable for [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169), $F(x) = F_a(\mathrm{arch}(x)) \prod_{v \in S'} F_{S'}(v)(x_v)$ whenever all components $x_v$ with $v \notin S'$ lie in the semi-local integral set, and $F(x) = 0$ whenever some component $x_v$ with $v \notin S'$ lies outside it, one has $\int F \, d\mu = c_G \bigl(\int F_a \, d\nu\bigr) \prod_{v \in S'} \int F_{S'}(v) \, d(\text{semi-local Haar})$.
--
--   Further, $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ is such that its norm string `normString`, the ordered product $\delta \cdot \sigma(\delta) \cdots \sigma^{[L:K]-1}(\delta)$ of the iterates of `sigmaGL` applied to $\delta$, is regular semisimple in the sense that $(\operatorname{tr})^2 - 4\det$ of its matrix is a unit (`hδ`). The twisted centralizer [`AutomorphicForm.twistedCentralizer`](def/AutomorphicForm_TwistedOrbital.html#L220) of an element $\delta'$ is the subgroup $\{t : t\delta' \sigma(t)^{-1} = \delta'\}$, with its Borel $\sigma$-algebra. The measures on centralizers are: a Haar measure $\tau$ on the twisted centralizer of $\delta$ over $\mathbb{A}_K$ (`hτ`), a Haar measure $\tau_a$ on the twisted centralizer of $\mathrm{arch}(\delta)$ over $\mathbb{A}_{K,\infty}$ (`hτa`), and for each finite place $v$ a Haar measure $\tau_f(v)$ on the twisted centralizer of $\delta_v$ (`hτf`) whose mass on the preimage of [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) under the inclusion of the subgroup is $1$ (`hτf1`). A constant $c_T > 0$ (`hcT`) is given together with the hypothesis `hT` that $\tau$ factorises with constant $c_T$ over $\tau_a$ and the $\tau_f(v)$, in exactly the same shape as `hG` but with the centralizers, their Borel structures and these measures in place of the ambient groups, $\nu$ and the semi-local Haar measures.
--
--   The weights are: a real-valued function $W_a$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ which is invariant under left translation by the twisted centralizer of $\mathrm{arch}(\delta)$ (`hWa`), continuous (`hWac`) and whose complexification is almost everywhere strongly $\nu$-measurable (`hWam`); and the semi-local weights [`AutomorphicForm.semiLocalWeight K L v`](def/AutomorphicForm_WeightedOrbitalRelation.html#L81), the finite sum over the places $w$ of $L$ above $v$ of the local logarithmic height weight `LocalWeight.weight` of the $w$-component, assumed invariant under left translation by the twisted centralizer of $\delta_v$ for every $v$ (`hWv`).
--
--   The test function data are a finite set $S$ of finite places of $K$ and functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $\varphi_a$ on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$, $\varphi_f$ on $\mathrm{GL}_2(\mathbb{A}_{L,\mathrm{fin}})$ and $\varphi_S(v)$ on the semi-local groups, subject to `hφ`, the predicate [`AutomorphicForm.IsSemiLocalFactorization`](def/AutomorphicForm_TwistedOrbital.html#L452): $\varphi_a$ is an archimedean test factor (it is $\Phi$ composed with the matrix entries in the mixed space for some smooth $\Phi$, and has compact support), $\varphi_f$ is locally constant with compact support, each $\varphi_S(v)$ with $v \in S$ is locally constant with compact support, $\varphi_f(h) = \prod_{v \in S}\varphi_S(v)(h_v)$ whenever all semi-local components $h_v$ with $v \notin S$ lie in the semi-local integral set, $\varphi_f(h) = 0$ whenever some such component lies outside it, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$.
--
--   Finally, $J \in \mathbb{C}$ satisfies `hJ`: $J$ is a twisted weighted orbital integral of $\varphi \circ$ [`AutomorphicForm.baseChangeGL`](def/AutomorphicForm_BaseChangePlaces.html#L69) at $\delta$ with respect to $\mu$ and $\tau$, for the global weight $x \mapsto W_a(\mathrm{arch}(x)) + \sum^{\mathrm{fin}}_{v} \mathrm{semiLocalWeight}(x_v)$ (finite sum over all finite places); that is, there is a section function $s \geq 0$, measurable, of compact support, with $\int_{\text{centralizer}} s(tx) \, d\tau = 1$ for every $x$ at which $\varphi(x^{-1}\delta\sigma(x))$ is nonzero, such that $J = \int \varphi(x^{-1}\delta \sigma(x)) \cdot W(x) \cdot s(x) \, d\mu$.
--
--   The conclusion is a disjunction. Either $J = 0$ and one of three degeneracies holds: (i) $\varphi_a$ composed with `archIdentGL` vanishes at $x^{-1} \cdot \mathrm{arch}(\delta) \cdot \sigma(x)$ for every $x$ in the archimedean group; or (ii) there is $v \in S$ with $\varphi_S(v)(x^{-1} \delta_v \sigma(x)) = 0$ for all $x$; or (iii) there is $v \notin S$ such that $x^{-1}\delta_v \sigma(x)$ lies outside [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) for all $x$.
--
--   Or else there exist a finite set $S_1$ of finite places with $S \subseteq S_1$, complex numbers $I_a$, $J_a$ and functions $I_v, J_v$ on the finite places such that: $I_a$ is a twisted orbital integral of $\varphi_a \circ$ `archIdentGL` at $\mathrm{arch}(\delta)$ with respect to $\nu$ and $\tau_a$; $J_a$ is a twisted weighted orbital integral of the same function with weight $W_a$, same measures; for every $v \in S$, $I_v(v)$ is a twisted orbital integral of $\varphi_S(v)$ at $\delta_v$ with respect to the semi-local Haar measure and $\tau_f(v)$, and $J_v(v)$ is the corresponding twisted weighted orbital integral with weight `semiLocalWeight`; for every $v \notin S$, the same two statements hold with $\varphi_S(v)$ replaced by the indicator function of the semi-local integral set with value $1$; $J_v(v) = 0$ for all $v \notin S_1$; and for every finite set $T$ of finite places with $S_1 \subseteq T$,
--   $$J = c_G \, c_T^{-1}\Bigl(J_a \prod_{v \in T} I_v(v) + I_a \sum_{v \in T} J_v(v) \prod_{u \in T \setminus \{v\}} I_u(u)\Bigr).$$
--
--   This is the weighted counterpart of the place-by-place factorisation of global twisted orbital integrals of factorizable test functions: because the weight attached to the non-invariant hyperbolic terms is a sum of local logarithmic height weights over the places, the weighted integral of a pure tensor expands by the Leibniz rule into a sum over places of one local weighted factor times plain factors elsewhere. It is used in the comparison of the weighted hyperbolic contributions on the two sides of the twisted trace formula, being cited by [`AutomorphicForm.twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization`](thm.html#AutomorphicForm.twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

open Classical

theorem AutomorphicForm.exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
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

    (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (hWa : ∀ t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
      ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        Wa ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) = Wa x)
    (hWac : Continuous Wa)
    (hWam : AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] (fun x => (Wa x : ℂ)) ν)
    (hWv : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ),
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x) =
          AutomorphicForm.semiLocalWeight K L v x)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (J : ℂ)
    (hJ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ
      (fun x => Wa (AutomorphicForm.tensorArch K L x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.tensorPlace K L v x))
      δ τ (φ ∘ AutomorphicForm.baseChangeGL K L) J) :
    (J = 0 ∧
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
      ∃ (Ia Ja : ℂ) (Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν
          (AutomorphicForm.tensorArch K L δ) τa (φa ∘ AutomorphicForm.archIdentGL K L) Ia ∧
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν Wa
          (AutomorphicForm.tensorArch K L δ) τa (φa ∘ AutomorphicForm.archIdentGL K L) Ja ∧
        (∀ v ∈ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (Iv v)) ∧
        (∀ v ∈ S, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (Jv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v)
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v)
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Jv v)) ∧
        (∀ v ∉ S₁, Jv v = 0) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u) := by sorry
