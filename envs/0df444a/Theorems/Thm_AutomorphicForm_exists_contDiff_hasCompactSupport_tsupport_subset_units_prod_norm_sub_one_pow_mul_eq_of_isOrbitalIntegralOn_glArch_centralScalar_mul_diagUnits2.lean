-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/4e04b5ec-7a1f-5e0c-87ab-6508d06a2dc1
-- title:
--   Archimedean window for split-torus orbital integrals on GL₂
-- statement:
--   Let $K$ be a number field, let $\nu_{Z_K}$ be a Haar measure on the idele group $(\mathbb A_K)^\times$ (with its Borel structure), let $u\in K^\times$ satisfy $u\neq 1$ in $K$, and let $f_\infty\colon \mathrm{GL}_2(K_\infty)\to\mathbb C$ be an archimedean test factor, i.e. $f_\infty$ has compact support and $f_\infty(g)=\Phi_0(\mathrm{archEntries}\,g)$ for some $C^\infty$ function $\Phi_0$ on $(\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to$ mixed space of $K)$. Let $\nu_A$ be a Haar measure on $\mathrm{GL}_2(K_\infty)$ for the Borel $\sigma$-algebra of its topology, and write $\gamma(z)=\mathrm{scalar}(z)\cdot\mathrm{diag}(\iota u,1)$ for $z\in(\mathbb A_K)^\times$, where $\iota\colon K\to\mathbb A_K$ is the structural map. Assume given: constants $c_\tau>0$ and $c_T>0$; Haar measures $\tau_G(z)$ on the centraliser of $\{\gamma(z)\}$ in $\mathrm{GL}_2(\mathbb A_K)$ satisfying the coupling $\int g\,d\tau_G(z)=c_\tau\int g(\mathrm{diag}(a,b))\,d(\nu_{Z_K}\otimes\nu_{Z_K})(a,b)$ for all $g\colon\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$; Haar measures $\tau_A(z)$ (Borel) on the centraliser of the archimedean component $\mathrm{glArch}(\gamma(z))$; Haar measures $\tau_F(z,v)$ (Borel) on the centraliser of the $v$-component of $\mathrm{glFin}(\gamma(z))$ in $\mathrm{GL}_2(K_v)$, each giving mass $1$ to the preimage of the set of matrices in $\mathrm{GL}_2$ that are integral at $v$; and the restricted-product formula: for every $z$, every finite set $S'$ of finite places and all $W$, $W_\infty$, $(W_v)_v$ with $W_\infty$ a.e. strongly measurable for $\tau_A(z)$ and $W_v$ a.e. strongly measurable for $\tau_F(z,v)$ ($v\in S'$), such that $W(t)=W_\infty(\mathrm{glArch}\,t)\prod_{v\in S'}W_v(t_v)$ whenever all components of $t$ outside $S'$ are integral and $W(t)=0$ whenever some component outside $S'$ is not, one has $\int W\,d\tau_G(z)=c_T\bigl(\int W_\infty\,d\tau_A(z)\bigr)\prod_{v\in S'}\int W_v\,d\tau_F(z,v)$. Then there is a function $\Phi$ on $\mathrm{Fin}\,2\to$ (mixed space of $K$), smooth and compactly supported, such that $\Phi(p)\neq 0$ forces both coordinates $p_0,p_1$ to correspond to units of $K_\infty$ under the ring isomorphism $\mathrm{InfiniteAdeleRing.ringEquiv\_mixedSpace}$; such that there is a compact set $C_a\subseteq (K_\infty^\times)^2$ with every $p$ in the topological support of $\Phi$ of the form $p=(\iota q_1,\iota q_2)$ for some $q\in C_a$; and such that for every $z\in(\mathbb A_K)^\times$ and every $I\in\mathbb C$ which is an orbital-integral value of $f_\infty$ at $\mathrm{glArch}(\gamma(z))$ relative to $\nu_A$ and $\tau_A(z)$ (that is, $I=\int f_\infty(x^{-1}\gamma x)\,w(x)\,d\nu_A(x)$ for some real-valued section weight $w$ as in `IsOrbitalIntegralOn`),
--   $$\Bigl(\prod_{w\mid\infty}\|u_w-1\|^{\,\mathrm{mult}(w)}\Bigr)\,I=\Phi\bigl(\iota(u_\infty),\iota(z_\infty)\bigr),$$
--   where $u_\infty$ and $z_\infty$ denote the archimedean components of $\iota u$ and of $z$.
--
--   This packages the archimedean contribution of the split conjugacy classes $\gamma(z)=\mathrm{scalar}(z)\,\mathrm{diag}(u,1)$ into a single smooth compactly supported window function of the pair (archimedean component of $u$, archimedean component of $z$), with support compactly contained in the units; the factor $\prod_{w\mid\infty}\|u_w-1\|^{\mathrm{mult}(w)}$ is the archimedean part of the Weyl discriminant. It is used in the integrability and weighted-class-integral statements that assemble the geometric side of the trace comparison from its local factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
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
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
            (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa I →
          ((∏ w : InfinitePlace K,
              ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
            Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] := by sorry
