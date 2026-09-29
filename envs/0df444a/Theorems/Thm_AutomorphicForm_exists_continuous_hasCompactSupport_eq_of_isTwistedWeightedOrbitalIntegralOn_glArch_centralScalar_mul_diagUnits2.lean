-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/6e9ff426-2c6b-5717-9055-ed236208f9dd
-- title:
--   One continuous compactly supported window for twisted archimedean orbital integrals
-- statement:
--   Fix a number field $K$, with $(\mathbb{A}_K)^\times$ carrying its Borel structure, and a Haar measure $\nu_{ZK}$ on $(\mathbb{A}_K)^\times$. Fix $u \in K^\times$ with $u \neq 1$, and write $\iota u$ for the image of $u$ in $(\mathbb{A}_K)^\times$ under the map induced by $K \to \mathbb{A}_K$. For $z \in (\mathbb{A}_K)^\times$ put $\gamma(z) := \mathrm{centralScalar}(z) \cdot \mathrm{diagUnits2}(\iota u, 1)$, the scalar matrix $z$ times $\mathrm{diag}(\iota u, 1)$ in $GL_2(\mathbb{A}_K)$; here [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) is the scalar embedding $(\mathbb{A}_K)^\times \to GL_2(\mathbb{A}_K)$ and `diagUnits2 x y` is the invertible diagonal matrix with entries $x, y$.
--
--   The $K$-side torus data consist of: a constant $c_{\tau K} > 0$; for each $z$ a Haar measure $\tau_G(z)$ on the centraliser of $\{\gamma(z)\}$ in $GL_2(\mathbb{A}_K)$ (hypotheses `hτG`, and `hτGc`, which asserts that for every $g : GL_2(\mathbb{A}_K) \to \mathbb{C}$ one has $\int_{Z(\gamma(z))} g(t)\,d\tau_G(z) = c_{\tau K} \int g(\mathrm{diagUnits2}(p_1,p_2))\, d(\nu_{ZK} \times \nu_{ZK})(p)$); for each $z$ a Haar measure $\tau_A(z)$ on the centraliser of the archimedean component $\mathrm{glArch}(\gamma(z))$ in $GL_2(\mathbb{A}_{K,\infty})$, for the Borel structure [`AutomorphicForm.centralizerBorel`](def/AutomorphicForm_TwistedOrbital.html#L62) (hypothesis `hτA`); for each $z$ and each height-one prime $v$ of $\mathcal{O}_K$ a Haar measure $\tau_F(z,v)$ on the centraliser of the $v$-component of $\mathrm{glFin}(\gamma(z))$ in $GL_2(K_v)$ (hypothesis `hτF`), normalised by `hτF1` so that the preimage in that centraliser of [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) — the set of $g \in GL_2(K_v)$ with both $g$ and $g^{-1}$ having entries in the valuation ring of $K_v$ — has measure $1$; and a constant $c_T > 0$ together with the factorisation hypothesis `hT`: for every $z$, every finite set $S'$ of height-one primes, every $W$ on $GL_2(\mathbb{A}_K)$, every $W_a$ on $GL_2(\mathbb{A}_{K,\infty})$ and every family $W_S(v)$ on $GL_2(K_v)$, if $W_a$ is almost everywhere strongly measurable for $\tau_A(z)$, each $W_S(v)$ with $v \in S'$ is almost everywhere strongly measurable for $\tau_F(z,v)$, $W(t) = W_a(\mathrm{glArch}\,t) \prod_{v \in S'} W_S(v)(t_v)$ for every $t$ in the centraliser of $\{\gamma(z)\}$ all of whose components outside $S'$ lie in `localIntegralSet`, and $W(t) = 0$ whenever some component of $t$ outside $S'$ fails to lie in `localIntegralSet`, then $\int W \, d\tau_G(z) = c_T \left(\int W_a \, d\tau_A(z)\right) \prod_{v \in S'} \int W_S(v)\, d\tau_F(z,v)$.
--
--   The extension data consist of a number field $L$ Galois over $K$ and $\sigma \in \mathrm{Gal}(L/K)$ such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (`hgen`), with $[L:K]$ prime (`hprime`).
--
--   The $L$-side archimedean data consist of: a function $\varphi_a$ on $GL_2(\mathbb{A}_{L,\infty})$ which is an archimedean test factor, i.e. $\varphi_a(g) = \Phi(\mathrm{archEntries}\,g)$ for some $C^\infty$ function $\Phi$ on $2 \times 2$ matrices over the mixed space of $L$, and $\varphi_a$ has compact support; a measure $\nu_A'$ on $GL_2(L \otimes_K \mathbb{A}_{K,\infty})$ for the Borel structure `glBorelOf`, assumed equal to the Haar measure [`AutomorphicForm.archHaarL K L`](def/AutomorphicForm_TwistedOrbital.html#L412); a family $\delta_A(z) \in GL_2(L \otimes_K \mathbb{A}_{K,\infty})$ such that (`hδA`) whenever $\mathrm{glArch}(\gamma(z))$ is a norm in the twisted sense — i.e. some $\delta$ and $y$ satisfy $\mathrm{toTensorGL}(\mathrm{glArch}\,\gamma(z)) = y^{-1} \, \mathrm{normString}_\sigma(\delta) \, y$, where $\mathrm{normString}_\sigma(\delta) = \prod_{i<[L:K]} \sigma^{i}_{GL}(\delta)$ — one has the exact identity $\mathrm{normString}_\sigma(\delta_A(z)) = \mathrm{toTensorGL}(\mathrm{glArch}\,\gamma(z))$; and Haar measures $\tau_A'(z)$ on the twisted centraliser $\{t : t \, \delta_A(z)\, \sigma_{GL}(t)^{-1} = \delta_A(z)\}$ (`hτA'`) which, whenever the same norm condition holds for $z$, are coupled to $\tau_A(z)$ through $y = 1$ (`hτA'c`): the pushforward of $\tau_A'(z)$ under $t \mapsto 1^{-1} t \, 1$ equals the pushforward of $\tau_A(z)$ under $t \mapsto \mathrm{toTensorGL}(t)$.
--
--   Under these hypotheses there exists a function $\Psi'$ on pairs (indexed by $\mathrm{Fin}\,2$) of points of the mixed space $\mathrm{mixedSpace}\,K$, with values in $\mathbb{C}$, such that the following hold. First, $\Psi'$ is continuous. Second, $\Psi'$ has compact support. Third, for every pair $p$ with $\Psi'(p) \neq 0$, both $(\mathrm{ringEquiv\_mixedSpace}\,K)^{-1}(p_0)$ and $(\mathrm{ringEquiv\_mixedSpace}\,K)^{-1}(p_1)$ are units of $\mathbb{A}_{K,\infty}$. Fourth, there is a compact subset $C_a$ of $(\mathbb{A}_{K,\infty})^\times \times (\mathbb{A}_{K,\infty})^\times$ such that every $p$ in the topological support of $\Psi'$ equals $\big(\mathrm{ringEquiv\_mixedSpace}\,K(q_1), \mathrm{ringEquiv\_mixedSpace}\,K(q_2)\big)$ for some $q \in C_a$. Fifth, for every $z \in (\mathbb{A}_K)^\times$ and every $J \in \mathbb{C}$: if $\mathrm{glArch}(\gamma(z))$ is a norm in the above sense, and $J$ satisfies the twisted weighted orbital integral relation `IsTwistedWeightedOrbitalIntegralOn` for the data $\sigma$, $\nu_A'$, the weight $$\lambda(y) = -\log H_L(\mathrm{archIdentGL}\,y) - \log H_L\big(\mathrm{glArch}(\mathrm{adelicWeyl}) \cdot \mathrm{archIdentGL}\,y\big),$$ with $H_L$ the archimedean height $\prod_{w \mid \infty} (|\det g_w| / \mathrm{rowNormSq}\,g_w)^{\mathrm{mult}(w)}$ and $\mathrm{adelicWeyl}$ the Weyl element $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ over $L$, at $\delta_A(z)$ with measure $\tau_A'(z)$ and test function $\varphi_a \circ \mathrm{archIdentGL}$ — that is, $J = \int \varphi_a(\mathrm{archIdentGL}(x^{-1} \delta_A(z) \sigma_{GL}(x)))\, \lambda(x)\, s(x) \, d\nu_A'(x)$ for some nonnegative measurable compactly supported $s$ with $\int_{t} s(tx) \, d\tau_A'(z) = 1$ at every $x$ where the integrand's test factor is nonzero — then $$J = \Psi'\big(\mathrm{ringEquiv\_mixedSpace}\,K(\mathrm{adeleArch}(\iota u)),\; \mathrm{ringEquiv\_mixedSpace}\,K(\mathrm{adeleArch}(z))\big),$$ the two arguments being the archimedean components of the adele attached to $u$ and of $z$, read in the mixed space. Sixth, for every $z$ such that $\mathrm{glArch}(\gamma(z))$ is not such a norm, the value of $\Psi'$ at that same pair of arguments is $0$.
--
--   This is the archimedean window on the twisted side of the comparison of weighted orbital integrals for cyclic base change for $GL(2)$: along the family of split classes $\mathrm{diag}(z\iota u, z)$ the twisted weighted orbital integral of a fixed archimedean test factor, with the logarithmic height weight, is exhibited as the value of a single continuous compactly supported function of the archimedean components of $u$ and $z$, which vanishes off the locus where the archimedean class is a twisted norm. It is used by the statements on integrability of window products, local constancy of the finite window values, and measurability of the window values in the central parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_continuous_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ z, (τG z).IsHaarMeasure)
    (hτGc : ∀ z, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA z))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z v, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z v))
    (hτF1 : ∀ z v, τF z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA z) →
        (∀ v ∈ S', AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S', WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG z) = cT * (∫ t, Wa t ∂(τA z)) * ∏ v ∈ S', ∫ t, WS v t ∂(τF z v))
    (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ z, (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA z)))
    (hτA' : ∀ z, (τA' z).IsHaarMeasure)
    (hτA'c : ∀ z, (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA z) 1 (τA z) (τA' z))
    :
    ∃ Ψ' : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      Continuous Ψ' ∧ HasCompactSupport Ψ' ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Ψ' p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ', ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
        (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
            (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
            (δA z) (τA' z) (φa ∘ AutomorphicForm.archIdentGL K L) J →
          J = Ψ' ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))]) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
          Ψ' ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] = 0) := by sorry
