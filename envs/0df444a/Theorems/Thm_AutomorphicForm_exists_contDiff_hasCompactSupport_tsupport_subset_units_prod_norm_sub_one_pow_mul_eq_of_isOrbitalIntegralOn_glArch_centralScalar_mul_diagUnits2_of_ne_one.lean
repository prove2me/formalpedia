-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9d394606-62bf-53b8-b91f-d9cde0af7e2c
-- title:
--   Uniform smooth archimedean window for split orbital integrals
-- statement:
--   Let $K$ be a number field, equipped with a measurable structure on the idele group $(\mathbb{A}_K)^\times$ that is the Borel structure of its topology, and let $\nu_{Z_K}$ be a Haar measure on $(\mathbb{A}_K)^\times$. Let $f_\infty : \mathrm{GL}_2(\mathbb{A}_{K,\infty}) \to \mathbb{C}$ satisfy [`AutomorphicForm.IsArchTestFactor`](def/AutomorphicForm_FactorizableTestFn.html#L27), i.e. $f_\infty$ has compact support and there is a $C^\infty$ function on $2\times 2$ matrices over the mixed space of $K$ computing $f_\infty(g)$ from the entries `archEntries` of $g$; let $c_\tau > 0$, and let $\nu_A$ be a Haar measure on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for the Borel structure `glBorelOf`. For $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$ put $\gamma(u,z) = \mathrm{scalar}(z)\cdot \mathrm{diag}(u,1) \in \mathrm{GL}_2(\mathbb{A}_K)$, where $u$ is viewed adelically. Assume given: measures $\tau_G(u,z)$ on the centraliser of $\{\gamma(u,z)\}$, Haar whenever $u \neq 1$, and coupled for $u \neq 1$ to $\nu_{Z_K}\otimes\nu_{Z_K}$ by $\int g \, d\tau_G(u,z) = c_\tau \int g(\mathrm{diag}(p_1,p_2))\, d(\nu_{Z_K}\times\nu_{Z_K})$ for every $g : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$; measures $\tau_A(u,z)$ on the centraliser of the archimedean component $\mathrm{glArch}\,\gamma(u,z)$, Haar for $u\neq 1$, for the Borel structure `centralizerBorel`; measures $\tau_F(u,z,v)$ on the local centraliser of the $v$-component of $\mathrm{glFin}\,\gamma(u,z)$ at each finite place $v$, Haar for $u \neq 1$ and of total mass $1$ on the preimage of the integral units set `localIntegralSet`. Assume finally a constant $c_T > 0$ and the restricted-product factorisation: for $u \neq 1$, any $z$, any finite set $S$ of finite places, and any $W$, $W_\infty$, $(W_v)_v$ with $W_\infty$ a.e. strongly measurable for $\tau_A(u,z)$, each $W_v$ ($v \in S$) a.e. strongly measurable for $\tau_F(u,z,v)$, $W(t) = W_\infty(\mathrm{glArch}\,t)\prod_{v\in S} W_v(t_v)$ whenever all components of $t$ outside $S$ lie in `localIntegralSet`, and $W(t) = 0$ otherwise, one has $\int W \, d\tau_G(u,z) = c_T \big(\int W_\infty \, d\tau_A(u,z)\big)\prod_{v\in S}\int W_v \, d\tau_F(u,z,v)$. Then there exists $\Phi : (\mathrm{Fin}\,2 \to \text{mixedSpace}(K)) \to \mathbb{C}$ which is $C^\infty$ over $\mathbb{R}$, has compact support, satisfies that $\Phi(p) \neq 0$ forces both coordinates $p_0, p_1$ to correspond to units of $\mathbb{A}_{K,\infty}$ under the ring equivalence with the mixed space, admits a compact set $C_\infty \subseteq (\mathbb{A}_{K,\infty}^\times)^2$ such that every point of $\mathrm{tsupport}\,\Phi$ is the pair of mixed-space images of some element of $C_\infty$, and such that for every $u \in K^\times$ with $u \neq 1$, every $z \in (\mathbb{A}_K)^\times$ and every $I \in \mathbb{C}$ which is an orbital-integral value of $f_\infty$ at $\mathrm{glArch}\,\gamma(u,z)$ relative to $\nu_A$ and $\tau_A(u,z)$ in the sense of [`AutomorphicForm.IsOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L248) (a real weight $w$ with `IsSectionFnOn` and $I = \int f_\infty(x^{-1}\gamma x)\,w(x)\, d\nu_A$), one has $$\Big(\prod_{w \mid \infty} \|u_w - 1\|^{\mathrm{mult}(w)}\Big)\, I = \Phi\big(u_\infty, z_\infty\big),$$ with $u_\infty, z_\infty$ the archimedean components of $u$ and $z$ read in the mixed space.
--
--   This is the archimedean window of the split torus family: the discriminant-normalised orbital integral of a fixed archimedean test factor at the regular split elements $\mathrm{scalar}(z)\,\mathrm{diag}(u,1)$ is realised by a single smooth, compactly supported function of the pair (ratio, centre) in the mixed space, supported on units, uniformly in $u \neq 1$ and in $z$; this is the Harish-Chandra descent to the split torus in adelic normalisation. It feeds the later class-sum and trace-formula computations, where the geometric side for hyperbolic classes is summed against such windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))
    :
    ∃ Φ : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
            (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) fa I →
          ((∏ w : InfinitePlace K,
              ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
            Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] := by sorry
