-- Prove2me | Theorems.Thm_AutomorphicForm_map_subtypeVal_eq_map_subtypeVal_of_forall_integral_centralizer_eq_mul_integral_prod
-- name    : AutomorphicForm.map_subtypeVal_eq_map_subtypeVal_of_forall_integral_centralizer_eq_mul_integral_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/f1c56935-ad6e-5b3e-92ee-f924c4f5d0b2
-- title:
--   Push-forward of archimedean centraliser measures is independent of z
-- statement:
--   Let $K$ be a number field, with a Borel measurable structure on the idele unit group $(\mathbb A_K)^\times$ and a Haar measure $\nu_{Z}$ on it; let $u\in K^\times$ with $u\neq 1$ in $K$, and let $c_\tau>0$. For an idele $z$ write $\gamma(z)=\mathrm{scalar}(z)\cdot\mathrm{diag}(u,1)\in GL_2(\mathbb A_K)$, the product of the scalar matrix attached to $z$ with the diagonal unit matrix built from the image of $u$ in $(\mathbb A_K)^\times$ and from $1$. Assume given: Haar measures $\tau_G(z)$ on the centraliser of $\{\gamma(z)\}$ in $GL_2(\mathbb A_K)$ such that for every function $g:GL_2(\mathbb A_K)\to\mathbb C$ one has $\int_{Z(\gamma(z))}g(t)\,d\tau_G(z)=c_\tau\iint g(\mathrm{diag}(p_1,p_2))\,d(\nu_Z\times\nu_Z)$; Haar measures $\tau_A(z)$ on the centraliser of the archimedean component $\gamma(z)_\infty$ in $GL_2(\mathbb A_{K,\infty})$ (Borel $\sigma$-algebra); Haar measures $\tau_F(z,v)$ on the centraliser of the $v$-component of $\gamma(z)$ in $GL_2(K_v)$ for each finite place $v$ (Borel $\sigma$-algebra), each giving mass $1$ to the preimage of [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), i.e. of `integralUnitsSet` of $\mathcal O_v$; and a constant $c_T>0$ together with the factorisation identity $\int W\,d\tau_G(z)=c_T\bigl(\int W_a\,d\tau_A(z)\bigr)\prod_{v\in S'}\int W_{S,v}\,d\tau_F(z,v)$, valid for every finite set $S'$ of finite places and all $W,W_a,(W_{S,v})$ with $W_a$ and the $W_{S,v}$ ($v\in S'$) a.e. strongly measurable, $W(t)=W_a(t_\infty)\prod_{v\in S'}W_{S,v}(t_v)$ whenever all components of $t$ outside $S'$ are integral, and $W(t)=0$ whenever some component outside $S'$ is not integral. Then for all ideles $z,z'$ the push-forwards of $\tau_A(z)$ and $\tau_A(z')$ along the inclusion of the respective centralisers into $GL_2(\mathbb A_{K,\infty})$ coincide.
--
--   This is the measure-normalisation step for the split family $\gamma(z)=\mathrm{scalar}(z)\,\mathrm{diag}(u,1)$: the restricted-product factorisation of Haar measure on a torus centraliser forces the archimedean factor, once transported into $GL_2(\mathbb A_{K,\infty})$, to be the same for all central twists $z$. It is used in the construction of twisted weighted orbital integrals on these classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_map_subtypeVal_eq_map_subtypeVal_of_forall_integral_centralizer_eq_mul_integral_prod.lean

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

theorem AutomorphicForm.map_subtypeVal_eq_map_subtypeVal_of_forall_integral_centralizer_eq_mul_integral_prod
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
    (z z' : (AdeleRing (𝓞 K) K)ˣ) :
    @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
        (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) Subtype.val (τA z) =
      @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
        (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) Subtype.val (τA z') := by sorry
