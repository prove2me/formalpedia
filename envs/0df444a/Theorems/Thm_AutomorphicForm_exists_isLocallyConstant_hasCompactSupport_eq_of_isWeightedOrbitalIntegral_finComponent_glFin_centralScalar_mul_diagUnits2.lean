-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/0b606d7f-eeb9-5f79-ac0a-c4120db86ca9
-- title:
--   Local weighted window of the split torus family at a finite place
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of $\mathcal{O}_K$, let $u \in K^\times$ with $u \neq 1$, and let $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, i.e. locally constant with compact support. For each idele unit $z \in (\mathbb{A}_K)^\times$ write $\gamma_v(z)$ for the $v$-component of the finite part of the adelic matrix $\mathrm{scalar}(z) \cdot \mathrm{diag}(u,1)$, where $\mathrm{scalar}(z)$ is the central element $z \cdot I_2$ and $u$ is viewed in $(\mathbb{A}_K)^\times$ via $K \to \mathbb{A}_K$; thus $\gamma_v(z) \in \mathrm{GL}_2(K_v)$. Suppose given, for every such $z$, a measure $\tau_F(z)$ on the centraliser of $\{\gamma_v(z)\}$ in $\mathrm{GL}_2(K_v)$ (with its Borel $\sigma$-algebra) which is a Haar measure and which assigns mass $1$ to the preimage under the inclusion of the set $\mathrm{GL}_2(\mathcal{O}_v)$-integral units. Then there is a function $\Psi_v$ on $K_v^\times \times K_v^\times$, locally constant and of compact support, such that for every $z$ and every $J \in \mathbb{C}$: if $J$ satisfies the weighted orbital integral relation [`AutomorphicForm.IsWeightedOrbitalIntegral`](def/AutomorphicForm_WeightedOrbitalRelation.html#L84) at $\gamma_v(z)$ for $f_v$ with respect to the normalised local Haar measure `localHaar K v`, the local weight `LocalWeight.weight` and the measure $\tau_F(z)$ on the centraliser, then $J = \Psi_v(u_v, z_v)$, where $u_v$ is the image of $u$ in $K_v^\times$ and $z_v$ is the $v$-component of the finite part of $z$.
--
--   This packages the weighted local orbital integrals along the family of split regular classes $z \cdot \mathrm{diag}(u,1)$, as $z$ varies over the ideles, into a single locally constant compactly supported window function of the pair $(u_v, z_v)$ at the finite place $v$. It is used in the local analysis of the weighted terms entering the trace-formula comparison, where the resulting window is shown to be integrable and measurable in products over places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (τF : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z))
    (hτF1 : ∀ z, τF z (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) :
    ∃ Ψv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Ψv ∧ HasCompactSupport Ψv ∧
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
        AutomorphicForm.IsWeightedOrbitalIntegral K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z) fv J →
          J = Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by sorry
