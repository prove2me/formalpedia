-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/fdfb031c-47f9-54bb-9c2d-3a8d23b26bc3
-- title:
--   A locally constant compactly supported twisted weighted local window at v
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra and $L/K$ Galois, let $v$ be a nonzero prime of $\mathcal O_K$, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and assume $[L:K]$ is prime. Let $u \in K^{\times}$ with $u \neq 1$ in $K$, and let $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb C$ be locally constant with compact support. For an idele unit $z$ write $\gamma(z)$ for the $v$-component of the image in $\mathrm{GL}_2$ of the finite adeles of the product of the scalar matrix with entry $z$ and $\mathrm{diag}(u,1)$, $u$ being sent into the adeles. Let $\delta_F$ assign to each idele unit $z$ an element $\delta_F(z) \in \mathrm{GL}_2(L \otimes_K K_v)$ such that, whenever some $\delta$ satisfies `IsNormOf` for $\gamma(z)$ (i.e. admits a norm conjugator), the norm string $\prod_{i<[L:K]} \sigma^i(\delta_F(z))$ (the $\sigma$-twisted product built from the induced action on $\mathrm{GL}_2(L \otimes_K K_v)$) equals the image of $\gamma(z)$ under $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$. Let $\tau_F'(z)$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser of $\delta_F(z)$, normalised so that the preimage of the semi-local integral units set has mass $1$. Then there is a locally constant, compactly supported $\Psi_v : K_v^{\times} \times K_v^{\times} \to \mathbb C$ such that for every idele unit $z$: if $\gamma(z)$ is a norm in the above sense, then every $J \in \mathbb C$ that is a twisted weighted orbital integral of $\varphi_v$ at $(\delta_F(z), \tau_F'(z))$, taken with respect to the semi-local Haar measure and semi-local weight, equals $\Psi_v(u_v, z_v)$, where $u_v$ is the image of $u$ in $K_v^{\times}$ and $z_v$ the $v$-component of $z$; and if $\gamma(z)$ is not such a norm, then $\Psi_v(u_v, z_v) = 0$.
--
--   This is the local, twisted weighted input at a finite place for the comparison of weighted orbital integrals on $\mathrm{GL}_2$ over $K$ and its cyclic prime-degree extension $L$: the values of the twisted weighted orbital integrals along the split classes $z\,\mathrm{diag}(u,1)$ are interpolated by a single locally constant compactly supported function of $(u_v, z_v)$, extended by zero off the norm locus. It feeds the integrability and local constancy statements for the window product used in the trace-formula comparison, and is cited by the results on integrability of the window bracket and on measurability of the window values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (δF : (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ z, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF z) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF z)))
    (hτF' : ∀ z, (τF' z).IsHaarMeasure)
    (hτF'1 : ∀ z, τF' z (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) :
    ∃ Ψv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Ψv ∧ HasCompactSupport Ψv ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
        (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
        AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF z) (τF' z) φv J →
          J = Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) = 0) := by sorry
