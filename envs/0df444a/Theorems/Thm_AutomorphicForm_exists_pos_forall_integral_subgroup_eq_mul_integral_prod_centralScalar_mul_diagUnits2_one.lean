-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_subgroup_eq_mul_integral_prod_centralScalar_mul_diagUnits2_one
-- name    : AutomorphicForm.exists_pos_forall_integral_subgroup_eq_mul_integral_prod_centralScalar_mul_diagUnits2_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/b427d254-6aba-5dd8-a956-6622ab16bd90
-- title:
--   Haar measure on the adelic diagonal torus via diag(p₁p₂,p₁)
-- statement:
--   Let $K$ be a number field, and equip the idele unit group $(\mathbb{A}_K)^\times$ (the units of `AdeleRing (𝓞 K) K`) with a measurable structure that is the Borel structure of its topology, and let $\nu_{Z_K}$ be a Haar measure on it; the group $GL_2(\mathbb{A}_K)$ carries its Borel $\sigma$-algebra. Let $D_K$ be a datum of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a monoid homomorphism from $K\simeq_{\mathrm{alg}[K]}K$ to the ring automorphisms of $\mathbb{A}_K$, compatible with $K\to\mathbb{A}_K$ and continuous in each member. Let $H_K\le GL_2(\mathbb{A}_K)$ be a subgroup whose underlying set is closed and which consists exactly of those $h$ whose matrix entries in positions $(1,0)$ and $(0,1)$ vanish and for which the image of $h$ under the entrywise action of $D_K.\mathrm{act}\,1$, multiplied by $h^{-1}$, lies in the centre of $GL_2(\mathbb{A}_K)$; since $D_K.\mathrm{act}$ is a monoid homomorphism, this last clause holds automatically, so $H_K$ is the diagonal torus. Let $\mu_{H_K}$ be a measure on $H_K$ that is both a Haar (hence left invariant) measure and right invariant. The assertion is that there exists a real $c_{H_K}>0$ such that for every function $g\colon GL_2(\mathbb{A}_K)\to\mathbb{C}$,
--   $$\int_{H_K} g(h)\,d\mu_{H_K}(h)\;=\;c_{H_K}\int_{(\mathbb{A}_K^\times)^2} g\bigl(p_1 I_2\cdot \mathrm{diag}(p_2,1)\bigr)\,d(\nu_{Z_K}\otimes\nu_{Z_K})(p),$$
--   where $p_1I_2$ is the central scalar matrix with entry $p_1$ and $\mathrm{diag}(p_2,1)$ is the diagonal unit matrix with entries $p_2$ and $1$; the product of the two is $\mathrm{diag}(p_1p_2,p_1)$. No measurability or integrability hypothesis is imposed on $g$: the Bochner integrals are those of Mathlib, which vanish on non-integrable functions.
--
--   This is the unfolding constant for the diagonal torus of $GL_2(\mathbb{A}_K)$: the map $(p_1,p_2)\mapsto \mathrm{diag}(p_1p_2,p_1)$ identifies $(\mathbb{A}_K^\times)^2$ with $H_K$, and Haar measure being unique up to a positive scalar, the two integrals agree up to a positive factor. It is used in the computation of the hyperbolic contributions to the trace formula on the $K$-side, by [`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine) and [`AutomorphicForm.exists_forall_hyperbolicSlope_eq_mul_sum_slotFamilyCoeff_mul_hyperbolicSlope_of_eq_affine`](thm.html#AutomorphicForm.exists_forall_hyperbolicSlope_eq_mul_sum_slotFamilyCoeff_mul_hyperbolicSlope_of_eq_affine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integral_subgroup_eq_mul_integral_prod_centralScalar_mul_diagUnits2_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_pos_forall_integral_subgroup_eq_mul_integral_prod_centralScalar_mul_diagUnits2_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (DK : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K)
    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K K DK 1 h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 K) K)))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant] :
    ∃ cHK : ℝ, 0 < cHK ∧
      ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
        ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
          cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK) := by sorry
