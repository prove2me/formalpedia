-- Prove2me | Theorems.Thm_AutomorphicForm_map_subtypeVal_centralizer_eq_and_map_conj_adelicWeyl_eq_of_forall_integral_eq_mul_integral_prod
-- name    : AutomorphicForm.map_subtypeVal_centralizer_eq_and_map_conj_adelicWeyl_eq_of_forall_integral_eq_mul_integral_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c488ead1-ba31-5328-b268-1ae4151d5f3d
-- title:
--   Uniform normalisation and Weyl symmetry of archimedean torus measures
-- statement:
--   Let $K$ be a number field, with the idele unit group $(\mathbb{A}_K)^\times$ carrying a measurable structure which is the Borel structure of its topology, and let $\nu_{Z_K}$ be a Haar measure on $(\mathbb{A}_K)^\times$. Write $\iota =$ `Units.map (algebraMap K (AdeleRing (𝓞 K) K))` for the induced map $K^\times \to (\mathbb{A}_K)^\times$, write $c(z) =$ [`AutomorphicForm.centralScalar (𝓞 K) K z`](def/AutomorphicForm_AdelicLsXi.html#L18) $= z \cdot I$ for the central scalar matrix in $GL_2(\mathbb{A}_K)$, and write $\operatorname{diag}(x,y) =$ `diagUnits2 x y` for the invertible diagonal matrix $!![x,0;0,y]$. The family of classes considered is
--   $$\gamma(u,z) = c(z)\cdot\operatorname{diag}(\iota u, 1) \in GL_2(\mathbb{A}_K), \qquad u \in K^\times,\ z \in (\mathbb{A}_K)^\times .$$
--   For each such pair there are three centralizer groups in play: the adelic one $\operatorname{Cent}(\{\gamma(u,z)\}) \le GL_2(\mathbb{A}_K)$; the archimedean one $\operatorname{Cent}(\{\mathrm{glArch}\,\gamma(u,z)\}) \le GL_2(\mathbb{A}_{K,\infty})$, where `AdelicLevel.glArch` is the map $GL_2(\mathbb{A}_K) \to GL_2(\mathbb{A}_{K,\infty})$ induced by the projection of the adeles to the infinite adeles, this group being equipped with the Borel structure [`AutomorphicForm.centralizerBorel`](def/AutomorphicForm_TwistedOrbital.html#L62); and, for each finite place $v$ of $K$, the local one [`AutomorphicForm.localCentralizer K v`](def/AutomorphicForm_LocalOrbitalBase.html#L193) $= \operatorname{Cent}(\{\gamma_v\}) \le GL_2(K_v)$, where $\gamma_v$ is the image of $\gamma(u,z)$ under `AdelicLevel.glFin` followed by `AdelicLevel.finComponent` at $v$, equipped with the Borel structure [`AutomorphicForm.localCentralizerBorel`](def/AutomorphicForm_LocalOrbitalBase.html#L197).
--
--   The data are: a real constant $c_{\tau K}$ with $0 < c_{\tau K}$ (`hcτK`); a family $\tau_G(u,z)$ of measures on the adelic centralizers, assumed Haar whenever $(u : K) \ne 1$ (`hτG`), and satisfying the *torus coupling* hypothesis `hτGc`: for all $u$ with $(u:K) \ne 1$, all $z$ and every function $g : GL_2(\mathbb{A}_K) \to \mathbb{C}$ (no measurability being assumed of $g$),
--   $$\int_{\operatorname{Cent}(\{\gamma(u,z)\})} g(t)\, d\tau_G(u,z) = c_{\tau K} \int_{(\mathbb{A}_K)^\times \times (\mathbb{A}_K)^\times} g(\operatorname{diag}(p_1,p_2))\, d(\nu_{Z_K} \otimes \nu_{Z_K})(p);$$
--   a family $\tau_A(u,z)$ of measures on the archimedean centralizers for the Borel structure just named, assumed Haar whenever $(u:K)\ne 1$ (`hτA`); a family $\tau_F(u,z,v)$ of measures on the local centralizers for their Borel structures, assumed Haar whenever $(u:K)\ne 1$ (`hτF`) and of total mass $1$ on the preimage under `Subtype.val` of the set [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) $\subseteq GL_2(K_v)$, the `integralUnitsSet` attached to the valuation ring $\mathcal{O}_v \subset K_v$ (`hτF1`); and a real constant $c_T$ with $0 < c_T$ (`hcT`).
--
--   Finally the *restricted-product factorisation* hypothesis `hT` is assumed: for all $u$, $z$, every finite set $S$ of finite places of $K$, every $W : GL_2(\mathbb{A}_K) \to \mathbb{C}$, every $W_\infty : GL_2(\mathbb{A}_{K,\infty}) \to \mathbb{C}$ and every family $W_v : GL_2(K_v) \to \mathbb{C}$, if $(u:K)\ne 1$, if $W_\infty$ is almost everywhere strongly measurable on the archimedean centralizer for $\tau_A(u,z)$, if $W_v$ is almost everywhere strongly measurable on the local centralizer at $v$ for $\tau_F(u,z,v)$ for each $v \in S$, if $W(t) = W_\infty(\mathrm{glArch}\, t)\prod_{v \in S} W_v(t_v)$ for every $t$ in the adelic centralizer all of whose components $t_v$ at places $v \notin S$ lie in [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), and if $W(t) = 0$ for every $t$ in the adelic centralizer having some component $t_v$, $v \notin S$, outside that set, then
--   $$\int W \, d\tau_G(u,z) = c_T \Bigl(\int W_\infty \, d\tau_A(u,z)\Bigr) \prod_{v \in S} \int W_v \, d\tau_F(u,z,v).$$
--
--   Under these hypotheses three conclusions are asserted. Write $\mathrm{val}_*$ for the pushforward along the inclusion `Subtype.val` of a centralizer into the ambient group, the target $GL_2(\mathbb{A}_{K,\infty})$ carrying the Borel structure [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), and let $w_\infty = \mathrm{glArch}(\mathrm{adelicWeyl})$ be the archimedean component of [`AutomorphicForm.adelicWeyl`](def/AutomorphicForm_WeylIntertwining.html#L35), the image in $GL_2(\mathbb{A}_K)$ of the Weyl element `gl2Weyl` of $GL_2(K)$.
--
--   (i) For all $u, u' \in K^\times$ and all $z, z' \in (\mathbb{A}_K)^\times$ with $(u:K)\ne 1$ and $(u':K)\ne 1$, the pushforwards agree: $\mathrm{val}_* \tau_A(u,z) = \mathrm{val}_* \tau_A(u',z')$ as measures on $GL_2(\mathbb{A}_{K,\infty})$.
--
--   (ii) For all $u$ with $(u:K) \ne 1$ and all $z$, the pushforward of $\tau_A(u,z)$ along $t \mapsto w_\infty\, t\, w_\infty^{-1}$ (from the archimedean centralizer into $GL_2(\mathbb{A}_{K,\infty})$) equals $\mathrm{val}_* \tau_A(u,z)$.
--
--   (iii) For all $u$ with $(u:K)\ne 1$ and all $z$, the measure attached to the conjugated parameter pair is the pullback of that Weyl transport: namely
--   $$\tau_A\bigl(u^{-1},\, z\,\iota u\bigr) = \mathrm{val}^{*}\Bigl( \bigl(t \mapsto w_\infty\, t\, w_\infty^{-1}\bigr)_* \tau_A(u,z)\Bigr),$$
--   where $\mathrm{val}^{*}$ denotes `Measure.comap` along the inclusion of $\operatorname{Cent}(\{\mathrm{glArch}(c(z\,\iota u)\cdot \operatorname{diag}(\iota u^{-1},1))\})$ into $GL_2(\mathbb{A}_{K,\infty})$, the left-hand side being the archimedean measure of the family at the pair $(u^{-1}, z\,\iota u)$.
--
--   This is the normalisation and symmetry input for the archimedean torus measures along the split family $\gamma(u,z) = c(z)\operatorname{diag}(\iota u, 1)$: the coupling and restricted-product hypotheses force the archimedean Haar measures to be normalised independently of $(u,z)$ after pushforward to $GL_2(\mathbb{A}_{K,\infty})$, and the resulting common measure to be invariant under conjugation by the Weyl element, with the third clause recording the same fact on the centralizer of the Weyl conjugate $\gamma(u^{-1}, z\,\iota u)$. It is used in the comparison of twisted orbital window values, in [`AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime`](thm.html#AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime). The proof cites the structural facts about adelic, archimedean and local centralizers of a single class (second countability, local compactness and the restricted-product description) together with the computation of `glArch` on $c(z)\operatorname{diag}(a,b)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_map_subtypeVal_centralizer_eq_and_map_conj_adelicWeyl_eq_of_forall_integral_eq_mul_integral_prod.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.map_subtypeVal_centralizer_eq_and_map_conj_adelicWeyl_eq_of_forall_integral_eq_mul_integral_prod
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (cτK : ℝ) (hcτK : 0 < cτK)
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
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
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
    (∀ (u u' : Kˣ) (z z' : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → (u' : K) ≠ 1 →
      @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
          (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) Subtype.val (τA u z) =
        @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)))
          (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) Subtype.val (τA u' z')) ∧
    (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
          (AutomorphicForm.glBorelOf (InfiniteAdeleRing K))
          (fun t => AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * (t : GL (Fin 2) (InfiniteAdeleRing K)) *
            (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹) (τA u z) =
        @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
          (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) Subtype.val (τA u z)) ∧
    (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      τA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
        @Measure.comap _ _
          (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)))
          (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) Subtype.val
          (@Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
            (AutomorphicForm.glBorelOf (InfiniteAdeleRing K))
            (fun t => AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * (t : GL (Fin 2) (InfiniteAdeleRing K)) *
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹) (τA u z))) := by sorry
