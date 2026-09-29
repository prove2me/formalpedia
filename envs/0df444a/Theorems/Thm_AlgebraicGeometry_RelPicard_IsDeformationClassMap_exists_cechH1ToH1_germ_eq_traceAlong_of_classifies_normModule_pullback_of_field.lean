-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f7a63b6e-ec5a-52b0-b868-03f0874c7d15
-- title:
--   Tangent action of a norm-pull-back endomorphism over a field
-- statement:
--   Let $K$ be a field, $c\colon C\to\operatorname{Spec}K$ a scheme over $K$ with a section $\varepsilon$ (a morphism $\operatorname{Spec}K\to C$ splitting $c$), and assume the base change $X'=C\times_{\operatorname{Spec}K}\operatorname{Spec}K$ is integral with projection $c'=\mathrm{pullback.snd}$ separated and smooth of relative dimension $1$; assume moreover every proper closed subset of $C$ is finite. Let $D$ be a relative $\operatorname{Pic}^0$ designation for $c$ (a $K$-scheme with structure morphism `D.toBase` and a zero section) and $h$ a datum exhibiting $D$ as representing the rigidified line bundles on $C\times_K T$ that are fibrewise algebraically equivalent to zero, with Poincaré bundle `h.poincare` and classifying maps `h.classify`. Let $y\colon Y\to\operatorname{Spec}K$ with $Y$ integral, $y$ proper and smooth of relative dimension $1$, and let $\pi_\alpha,\pi_\beta\colon Y\to C$ satisfy $\pi_\alpha\circ$, $\pi_\beta$ composed with $c$ equal $y$, with $\pi_\alpha$ finite, flat and locally of finite presentation of constant rank $d$ at every point and $\pi_\beta$ affine; let $\pi_{\alpha 1},\pi_{\beta 1}\colon Y\to X'$ be the induced lifts, compatible with both projections. Let $\varphi_1$ be an endomorphism of $D$ over $\operatorname{Spec}K$ which, by hypothesis `hmoduli`, classifies on $T$-points the operation $M\mapsto$ the rigidification along `rigSection` of $\mathrm{normModule}$ (the $d$-th determinant of the pushforward along the base change of $\pi_\alpha$, tensored with the dual of the corresponding determinant for the unit module) applied to the pullback of $M$ along the base change of $\pi_\beta$. Let $\mathcal W$ be a two-affine open cover of $C$, and $\delta$ a deformation-class map at $A=K$: for every rigidified bundle on $C\times_K K[\epsilon]$ with trivial reduction, any pair of frames over the two charts whose transition is $1+\epsilon f$ forces $\delta$ of its class to be the Čech class of $f$. Let $x$, $x_r$ be $K[\epsilon]$-points of $D$ whose reductions modulo $\epsilon$ equal the identity of the relative group law, with $x_r$ equal to $x$ followed by $\varphi_1$, and let $s\in\Gamma(X',W_0\cap W_1)$ (where $W=\mathcal W$ pulled back) represent $\delta$ of the class of $x$. Then, assuming $W_0\cap W_1$ nonempty, for all $K$-algebra maps $\varphi_\alpha,\varphi_\beta\colon K(X')\to K(Y)$ inducing $\pi_{\alpha 1},\pi_{\beta 1}$ on generic stalks, both integral, with the trace along $\varphi_\alpha$ integral place by place, such that the place sets of $W_0$ and $W_1$ cover all places of $K(X')$ and the generic germ of $s$ lies in the space $L(0)$ on the intersection of those place sets, there exist a section $s_r\in\Gamma(X',W_0\cap W_1)$ whose generic germ again lies in that $L(0)$ and a Čech class $x'$ in $H^1$ for the $\varphi_\alpha$-preimages of the two place sets and the zero divisor on $K(Y)$, such that $\delta$ of the class of $x_r$ is the class of $s_r$, the image of $x'$ in $H^1(0)$ over $K(Y)$ agrees with the image of the $\varphi_\beta$-pullback of the class of the germ of $s$, and the image in $H^1(0)$ over $K(X')$ of the class of the germ of $s_r$ equals the image of the trace along $\varphi_\alpha$ of $x'$.
--
--   This is the field-base form of the statement that the endomorphism of the relative $\operatorname{Pic}^0$ given by norm along $\pi_\alpha$ after pull-back along $\pi_\beta$ acts on the tangent space, identified with $H^1$ of the structure sheaf in Čech form, by pull-back followed by trace on répartition classes. It feeds the companion statement with $\pi_\beta$ a monomorphism, which is the shape used for the Hecke correspondences on Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.Scheme.TwoAffineOpenCover
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
    (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    [IsIntegral (Limits.pullback c (specMap K K))]
    [IsSeparated (pullback.snd c (specMap K K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (specMap K K))]

    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (D : RelativePic0Designation K c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y) (Hβ : πβ ≫ c = y)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα] [IsAffineHom πβ]
    (d : ℕ) (hd : ∀ z, πα.finrank z = d)
    (πα₁ πβ₁ : Y ⟶ Limits.pullback c (specMap K K))
    (hα₁ : πα₁ ≫ pullback.fst c (specMap K K) = πα) (hα₁' : πα₁ ≫ pullback.snd c (specMap K K) = y)
    (hβ₁ : πβ₁ ≫ pullback.fst c (specMap K K) = πβ) (hβ₁' : πβ₁ ≫ pullback.snd c (specMap K K) = y)

    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hmoduli :
      ∀ (T : Scheme.{u}) (t : T ⟶ Spec (.of K))
          (M : RigidifiedLineBundle c ε t) (hM : (algEquivZeroCut c ε).P t M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify t M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
            (Scheme.Modules.normModule (curveChange (c' := y) πα Hα t) d
              ((Scheme.Modules.pullback (curveChange (c' := y) πβ Hβ t)).obj M.L))))

    (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲} (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (x xr : {x : SchemeHomOver (specMap K (DualNumber K)) D.toBase //
        dualNumberReduction K K ≫ x.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (specMap K K)).1})
    (hxr : xr.1.1 = x.1.1 ≫ φ₁.1)
    (s : ((𝒲.pullback c K).cover (pullback.snd c (specMap K K))).A01)
    (hs : δ (h.kerPointsToRigKer K x) = Submodule.Quotient.mk s) :
    letI X' := Limits.pullback c (specMap K K)
    letI c' : X' ⟶ Spec (.of K) := pullback.snd c (specMap K K)
    letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    letI W := 𝒲.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)]

      (φα φβ : X'.functionField →ₐ[K] Y.functionField)
      (hφπα : Y.fromSpecStalk (genericPoint Y) ≫ πα₁ =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφπβ : Y.fromSpecStalk (genericPoint Y) ≫ πβ₁ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong φα hφα)
      (hW : AlgebraicCurve.placesOf c' W.U0 ∪ AlgebraicCurve.placesOf c' W.U1 = Set.univ)
      (hsr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      ∃ (sr : ((𝒲.pullback c K).cover (pullback.snd c (specMap K K))).A01)
        (hsrr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom sr ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
            (0 : AlgebraicCurve.Divisor K X'.functionField))
        (x' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf c' W.U0)
          ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K Y.functionField)),
        δ (h.kerPointsToRigKer K xr) = Submodule.Quotient.mk sr ∧
        AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) 0 x' =
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW) 0
            (AlgebraicCurve.cechH1.pullbackAlong φβ hφβ _ _
              (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩)) ∧
        AlgebraicCurve.cechH1ToH1 hW 0
            (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom sr, hsrr⟩) =
          AlgebraicCurve.cechH1ToH1 hW 0 (AlgebraicCurve.cechH1.traceAlong φα hφα htrα _ _ x') := by sorry
