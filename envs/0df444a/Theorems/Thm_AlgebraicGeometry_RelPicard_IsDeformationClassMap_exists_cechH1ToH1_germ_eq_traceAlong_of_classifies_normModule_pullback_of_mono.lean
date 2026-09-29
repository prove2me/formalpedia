-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f9259173-309a-5a02-9b6b-0ede9953abc8
-- title:
--   Norm–pull-back endomorphism acts by trace on Čech H¹
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ c=\mathrm{id}$), and let $K$ be a field that is an $R$-algebra with $\operatorname{Spec}K\to\operatorname{Spec}R$ a monomorphism; put $X'=C\times_{\operatorname{Spec}R}\operatorname{Spec}K$ with second projection $c'$, assumed integral, with $c'$ separated and smooth of relative dimension $1$, and assume every closed subset of $X'$ other than the whole space is finite. Let $D$ consist of a scheme over $\operatorname{Spec}R$ with a zero section, and let $h$ witness that $D$ represents the functor of rigidified line bundles on $C\times_R T$ that are fibrewise algebraically equivalent to zero, with Poincaré bundle $h.\mathrm{poincare}$ and classifying maps $h.\mathrm{classify}$. Let $y\colon Y\to\operatorname{Spec}K$ be integral, proper and smooth of relative dimension $1$, and $\pi_\alpha,\pi_\beta\colon Y\to C$ morphisms over $R\to K$ whose induced $K$-morphisms $Y\to X'$ are respectively finite, flat and locally of finite presentation of constant fibre rank $d$, and affine. Let $\varphi_1$ be an endomorphism of $D$ over $\operatorname{Spec}R$ which, by hypothesis `hmoduli`, classifies on all $K$-schemes $T$ the operation sending a fibrewise-algebraically-trivial rigidified bundle $M$ to the rigidification (along `rigSection`) of $\mathrm{normModule}$ in degree $d$ along the $\pi_\alpha$-base change of the pull-back of $M.L$ along the $\pi_\beta$-base change; that is, the pull-back of the Poincaré bundle along $h.\mathrm{classify}(M)$ followed by $\varphi_1$ is isomorphic to that bundle. Let $\mathcal W$ be a two-affine open cover of $C$ (two affine opens covering $C$ with affine intersection), $\delta$ a deformation-class map assigning to a class in `RigKerDualNumber c ε K` a class in the Čech $H^1$ of the structure sheaf for the pulled-back cover $W=\mathcal W.\mathrm{pullback}\,c\,K$ on $X'$, in the sense of `IsDeformationClassMap` (on a bundle trivialised by frames $e_0,e_1$ whose comparison on the overlap is $1+\epsilon f$, $\delta$ returns the class of $f$). Let $x,x_r$ be $K[\epsilon]$-points of $D$ reducing to the unit of the group law attached to $h$, with $x_r=x$ followed by $\varphi_1$, and let $s$ be a section on the overlap of $W$ with $\delta(h.\mathrm{kerPointsToRigKer}\,K\,x)=[s]$. Assume the overlap $W.U_0\cap W.U_1$ is nonempty, and let $\varphi_\alpha,\varphi_\beta\colon K(X')\to K(Y)$ be $K$-algebra maps (function fields taken via `baseToFunctionField`) inducing the two morphisms $Y\to X'$ on generic stalks, with $\varphi_\alpha,\varphi_\beta$ integral and with $\varphi_\alpha$ satisfying `TraceIntegralAlong` (the trace of an element integral at all places above $v$ is integral at $v$). Assume the sets $S_0,S_1$ of places of $K(X')$ centred at closed points of $W.U_0$, $W.U_1$ cover all places, and that the germ of $s$ at the generic point lies in $L(0)$ on $S_0\cap S_1$. Then there exist a section $s_r$ on the overlap whose germ also lies in $L(0)$ on $S_0\cap S_1$, and a class $x'$ in the Čech $H^1$ of the divisor $0$ for the $\varphi_\alpha$-preimages of $S_0,S_1$ among places of $K(Y)$, such that $\delta(h.\mathrm{kerPointsToRigKer}\,K\,x_r)=[s_r]$; the image of $x'$ in $H^1(0)$ over $K(Y)$ equals the image of the $\varphi_\beta$-pull-back of the class of the germ of $s$; and the image of the class of the germ of $s_r$ in $H^1(0)$ over $K(X')$ equals the image of the $\varphi_\alpha$-trace of $x'$.
--
--   This is the $H^1$-side of the Hecke correspondence: the deformation (tangent) class at the origin of the Jacobian endomorphism classified by $\mathrm{Nm}_{\pi_\alpha}\circ\pi_\beta^{*}$ is computed as the trace along $\varphi_\alpha$ of the pull-back along $\varphi_\beta$, the identification taking place in $H^1$ of the divisor $0$ read in the function fields. It is stated over a general base ring $R$ with a field $K$ above it, and is obtained from the corresponding statement over a field together with the base-change comparison for the representing object and for the deformation-class map; it is used in the computation of the Serre pairing against Hecke generators on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono.lean

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.Scheme.TwoAffineOpenCover
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [Field K] [Algebra R K]

    [Mono (specMap R K)]
    [IsIntegral (Limits.pullback c (specMap R K))]
    [IsSeparated (pullback.snd c (specMap R K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (specMap R K))]

    (hC : ∀ Z : Set ↥(Limits.pullback c (specMap R K)), IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y ≫ specMap R K) (Hβ : πβ ≫ c = y ≫ specMap R K)
    [IsFinite (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [Flat (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [LocallyOfFinitePresentation (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [IsAffineHom (pullback.lift πβ y Hβ : Y ⟶ Limits.pullback c (specMap R K))]
    (d : ℕ) (hd : ∀ z, (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K)).finrank z = d)

    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hmoduli :
      ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (.of K))
          (M : RigidifiedLineBundle c ε (t' ≫ specMap R K))
          (hM : (algEquivZeroCut c ε).P (t' ≫ specMap R K) M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify (t' ≫ specMap R K) M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c (t' ≫ specMap R K) ε) (pullback.snd c (t' ≫ specMap R K))
            (Scheme.Modules.normModule (curveChange (c' := y ≫ specMap R K) πα Hα (t' ≫ specMap R K)) d
              ((Scheme.Modules.pullback (curveChange (c' := y ≫ specMap R K) πβ Hβ (t' ≫ specMap R K))).obj M.L))))

    (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲} (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (x xr : {x : SchemeHomOver (specMap R (DualNumber K)) D.toBase //
        dualNumberReduction R K ≫ x.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (specMap R K)).1})
    (hxr : xr.1.1 = x.1.1 ≫ φ₁.1)
    (s : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01)
    (hs : δ (h.kerPointsToRigKer K x) = Submodule.Quotient.mk s) :
    letI X' := Limits.pullback c (specMap R K)
    letI c' : X' ⟶ Spec (.of K) := pullback.snd c (specMap R K)
    letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    letI W := 𝒲.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)]

      (φα φβ : X'.functionField →ₐ[K] Y.functionField)
      (hφπα : Y.fromSpecStalk (genericPoint Y) ≫ pullback.lift πα y Hα =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφπβ : Y.fromSpecStalk (genericPoint Y) ≫ pullback.lift πβ y Hβ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong φα hφα)
      (hW : AlgebraicCurve.placesOf c' W.U0 ∪ AlgebraicCurve.placesOf c' W.U1 = Set.univ)
      (hsr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      ∃ (sr : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01)
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
