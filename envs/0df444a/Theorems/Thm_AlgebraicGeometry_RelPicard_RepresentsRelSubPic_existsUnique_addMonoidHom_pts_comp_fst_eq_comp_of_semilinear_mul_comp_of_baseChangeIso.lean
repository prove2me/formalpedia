-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f4cc5e4e-73e6-5131-afa0-0a22e73377d7
-- title:
--   Semilinear group endomorphism induces a unique additive endomorphism of J
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Let $D$ be a relative $\operatorname{Pic}^0$ designation for $c$: a scheme $D.P$ with structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec}R$ and a section $D.\mathrm{zeroSection}$ of it. Assume $h$ witnesses that $D$ represents, in the sense of `RepresentsRelSubPic`, the subfunctor of rigidified line bundles on $c$ cut out by the condition `algEquivZeroCut c ε` (whose predicate is `FibrewiseAlgEquivZero`): thus $h$ provides a Poincaré bundle $h.\mathrm{poincare}$ on the base change of $c$ along $D.\mathrm{toBase}$ satisfying that condition, the universal property that every such rigidified bundle over a base $t\colon T\to\operatorname{Spec}R$ is induced by a unique $T$-point of $D.\mathrm{toBase}$, and triviality of the pullback along the zero section. Let $R'$ be an $R$-algebra and suppose $hR$ is such a representability witness for the base-changed curve $\mathrm{baseChange}\,R\,c\,R'=\mathrm{pr}_2\colon C\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to\operatorname{Spec}R'$, its induced section $\mathrm{sectionBaseChange}\,R'\,\varepsilon$, the corresponding cut condition, and the base-changed designation $D.\mathrm{baseChange}\,R'$, whose total space is $D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'$. Assume moreover that the Poincaré bundle of $hR$ is isomorphic, as a line bundle, to the $R'$-base change (`BaseChange.ofR`) of the pullback of $h.\mathrm{poincare}$ along the first projection $\mathrm{pr}_1\colon D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to D.P$. Let $J$ be an additive abelian group equipped with a bijection $\mathrm{pts}$ from $J$ to the set of sections of $(D.\mathrm{baseChange}\,R').\mathrm{toBase}$ over the identity of $\operatorname{Spec}R'$, such that for all $a,b\in J$ the pullback of the Poincaré bundle of $hR$ along $\mathrm{pts}(a+b)$ is isomorphic to the tensor product of its pullbacks along $\mathrm{pts}(a)$ and $\mathrm{pts}(b)$. Let $\sigma\colon R\to R$ be a ring endomorphism with $(\text{algebraMap }R\,R')\circ\sigma=\text{algebraMap }R\,R'$, and let $\chi$ be a morphism $D.P\to D.P$ which is $\sigma$-semilinear, i.e. $\chi$ followed by $D.\mathrm{toBase}$ equals $D.\mathrm{toBase}$ followed by $\operatorname{Spec}\sigma$. Assume $\chi$ is a homomorphism for the relative group law `relativeGroupLaw` attached to $h$ and the group condition `algEquivZeroGroupCut c ε`: for every scheme $T$, every $s\colon T\to\operatorname{Spec}R$ and all $T$-points $x,y$ of $D.\mathrm{toBase}$ over $s$, the product $m_s(x,y)$ followed by $\chi$ equals $m_{s\circ\operatorname{Spec}\sigma}(x\chi,y\chi)$, where $x\chi,y\chi$ denote $x$ and $y$ followed by $\chi$. Then there is a unique additive homomorphism $e\colon J\to J$ such that for every $y\in J$ the composite of $\mathrm{pts}(e\,y)$ with $\mathrm{pr}_1$ equals the composite of $\mathrm{pts}(y)$ with $\mathrm{pr}_1$ followed by $\chi$.
--
--   This is the semilinear version of the transfer of an endomorphism of a representing scheme of the relative $\operatorname{Pic}^0$ to the abelian group of points recorded by a dictionary $\mathrm{pts}$: a $\sigma$-semilinear group endomorphism $\chi$ of the model, with $\sigma$ acting trivially on $R'$, induces a well-defined additive endomorphism of $J$. It is used in the construction of Hecke and Galois operators on the points of the Jacobian model of $X_1(Mp)$ in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (J : Type u) [AddCommGroup J]
    (pts : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (D.baseChange R').toBase)
    (hadd : ∀ a b : J, Nonempty
      ((hR.poincare.pullbackAlong (pts (a + b))).L ≅
        (hR.poincare.pullbackAlong (pts a)).L ⊗ (hR.poincare.pullbackAlong (pts b)).L))
    (σ : R →+* R) (hσ : (algebraMap R R').comp σ = algebraMap R R')
    (χ : SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom σ)) D.toBase)
    (hχmul : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y).1 ≫ χ.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (s ≫ Spec.map (CommRingCat.ofHom σ))
          ⟨x.1 ≫ χ.1, by rw [Category.assoc, χ.2, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ χ.1, by rw [Category.assoc, χ.2, ← Category.assoc, y.2]⟩).1) :
    ∃! e : J →+ J, ∀ y : J,
      (pts (e y)).1 ≫ pullback.fst D.toBase (specMap R R') = ((pts y).1 ≫ pullback.fst D.toBase (specMap R R')) ≫ χ.1 := by sorry
