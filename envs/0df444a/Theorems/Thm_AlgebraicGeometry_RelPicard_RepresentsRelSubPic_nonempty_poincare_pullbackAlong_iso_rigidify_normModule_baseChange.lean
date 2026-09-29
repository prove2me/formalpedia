-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2e437084-1063-577d-805a-5a440bf8d7c7
-- title:
--   Moduli description of an endomorphism transported to the base change
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a scheme over $R$ and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\,{\ggg}\,c=\mathrm{id}$), and let $K$ be a commutative $R$-algebra for which $\operatorname{Spec}K\to\operatorname{Spec}R$ is a monomorphism. Let $D$ consist of a scheme $P$ with a structure morphism $P\to\operatorname{Spec}R$ and a zero section, and let $h$ witness that $D$ represents the condition `algEquivZeroCut` on rigidified line bundles over $(c,\varepsilon)$ — i.e. $h$ supplies a Poincaré rigidified bundle $\mathcal P$ on $C\times_R P$ lying in the cut, for each $t\colon T\to\operatorname{Spec}R$ and each rigidified $\mathcal M$ on $C\times_R T$ in the cut a unique classifying map $\mathrm{cl}_{\mathcal M}\colon T\to P$ over $\operatorname{Spec}R$ with $\mathrm{cl}_{\mathcal M}^\ast\mathcal P\cong\mathcal M$, and triviality of $\mathcal P$ along the zero section; let $h'$ be the corresponding datum for $C_K=C\times_R\operatorname{Spec}K$ with its induced section and for $D_K=P\times_{\operatorname{Spec}R}\operatorname{Spec}K$, with Poincaré bundle $\mathcal P'$, and assume $\mathcal P'$ is isomorphic to the transport `BaseChange.ofR` of the pullback of $\mathcal P$ along the projection $\mathrm{pr}_1\colon P\times_R\operatorname{Spec}K\to P$. Let $y\colon Y\to\operatorname{Spec}K$ and $\pi_\alpha,\pi_\beta\colon Y\to C$ satisfy $\pi_\alpha\,{\ggg}\,c=\pi_\beta\,{\ggg}\,c=y\,{\ggg}\,\operatorname{Spec}(R\to K)$, and let $\pi_{\alpha,1},\pi_{\beta,1}\colon Y\to C_K$ be the induced morphisms, with $\pi_{\alpha,1}$ finite, flat and locally of finite presentation of constant fibre rank $d$. Let $\varphi_1\colon P\to P$ be a morphism over $\operatorname{Spec}R$ such that for every $K$-scheme $t'\colon T\to\operatorname{Spec}K$ and every rigidified line bundle $\mathcal M$ on $C\times_RT$ in the cut, the pullback of $\mathcal P$ along $\mathrm{cl}_{\mathcal M}$ followed by $\varphi_1$ has underlying module isomorphic to the rigidification, along the section `rigSection` and the projection $C\times_RT\to T$, of the norm module of degree $d$ of $(\pi_{\beta}\times T)^\ast\mathcal M$ along $\pi_\alpha\times T$; here the norm module of $\pi$ is $\det_d(\pi_\ast L)\otimes\det_d(\pi_\ast\mathcal O)^\vee$ and $\mathrm{rigidify}(\sigma,q,L)=L\otimes q^\ast(\sigma^\ast L)^\vee$. Let finally $\varphi_{1,K}\colon D_K\to D_K$ be a morphism over $\operatorname{Spec}K$ with $\varphi_{1,K}\,{\ggg}\,\mathrm{pr}_1=\mathrm{pr}_1\,{\ggg}\,\varphi_1$, together with the identities $\pi_{\alpha,1}\,{\ggg}\,(C_K\to\operatorname{Spec}K)=y$ and likewise for $\pi_{\beta,1}$. Then for every $K$-scheme $t\colon T\to\operatorname{Spec}K$ and every rigidified line bundle $\mathcal M$ on $C_K\times_KT$ satisfying the cut condition over $K$, the pullback of $\mathcal P'$ along the classifying map of $\mathcal M$ followed by $\varphi_{1,K}$ has underlying module isomorphic to the rigidification, along `rigSection` and the projection $C_K\times_KT\to T$, of the degree-$d$ norm module along $\pi_{\alpha,1}\times T$ of the pullback of $\mathcal M$ along $\pi_{\beta,1}\times T$.
--
--   This is the base-change step for the moduli-theoretic description of an endomorphism of the scheme representing the rigidified $\mathrm{Pic}^0$-type cut: an endomorphism given on moduli by the correspondence $\mathcal M\mapsto \mathrm{Nm}_{\pi_\alpha}\pi_\beta^\ast\mathcal M$ over $R$ is still so described, over $K$, by the induced endomorphism of the base-changed designation. It feeds the hypothesis binder of [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono), where such a correspondence is compared with its effect on deformation classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicCurve Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K] [Mono (specMap R K)]
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K))
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y ≫ specMap R K) (Hβ : πβ ≫ c = y ≫ specMap R K)
    [IsFinite (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [Flat (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [LocallyOfFinitePresentation (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
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
    (φ₁K : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hφ₁K : φ₁K.1 ≫ pullback.fst D.toBase (specMap R K) = pullback.fst D.toBase (specMap R K) ≫ φ₁.1)
    (Hα₁ : pullback.lift πα y Hα ≫ SmoothProperCurve.baseChange R c K = y)
    (Hβ₁ : pullback.lift πβ y Hβ ≫ SmoothProperCurve.baseChange R c K = y)
    (T : Scheme.{u}) (t : T ⟶ Spec (.of K))
    (M : RigidifiedLineBundle (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε) t)
    (hM : (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)).P t M) :
    Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp (h'.classify t M hM) φ₁K)).L ≅
      Scheme.Modules.rigidify
        (rigSection (SmoothProperCurve.baseChange R c K) t (SmoothProperCurve.sectionBaseChange K ε))
        (pullback.snd (SmoothProperCurve.baseChange R c K) t)
        (Scheme.Modules.normModule (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) d
          ((Scheme.Modules.pullback (curveChange (c' := y) (pullback.lift πβ y Hβ) Hβ₁ t)).obj M.L))) := by sorry
