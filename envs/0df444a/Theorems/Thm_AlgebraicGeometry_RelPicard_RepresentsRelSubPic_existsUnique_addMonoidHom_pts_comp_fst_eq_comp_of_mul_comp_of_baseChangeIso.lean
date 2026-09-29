-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_mul_comp_of_baseChangeIso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_mul_comp_of_baseChangeIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/72cbf132-69ea-5d56-8101-1f3a378995ba
-- title:
--   Endomorphism of Pic⁰ induces unique additive endomorphism of J
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ c=\mathrm{id}$). Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec}R$ and a zero section, and let $h$ witness that $D$ represents the functor of rigidified line bundles on $C\times_R(-)$ that are fibrewise algebraically trivial (over every algebraically closed field point of the base): $h$ provides a Poincaré bundle on $C\times_R D.P$ satisfying that condition, the universal property that every such rigidified bundle over $t\colon T\to\operatorname{Spec}R$ is the pullback of the Poincaré bundle along a unique $T\to D.P$ over $\operatorname{Spec}R$, and a trivialisation along the zero section. Let $R'$ be a commutative $R$-algebra and let $hR$ be the corresponding witness for the base-changed curve $C\times_R R'\to\operatorname{Spec}R'$ with the base-changed section and the designation $D.\mathrm{baseChange}\,R'$, whose total space is $D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'$. Assume ($hPR$) that the Poincaré bundle of $hR$ is isomorphic to the $R'$-base change of the pullback of $h$'s Poincaré bundle along the first projection $D.P\times_R\operatorname{Spec}R'\to D.P$. Let $J$ be an additive abelian group and $\mathrm{pts}$ a bijection from $J$ onto the sections of $(D.\mathrm{baseChange}\,R').\mathrm{toBase}$ over $\mathrm{id}_{\operatorname{Spec}R'}$, such that for all $a,b\in J$ the bundle obtained by pulling back $hR$'s Poincaré bundle along $\mathrm{pts}(a+b)$ is isomorphic to the tensor product of those obtained from $\mathrm{pts}(a)$ and $\mathrm{pts}(b)$. Let $\psi\colon D.P\to D.P$ satisfy $\psi$ followed by $D.\mathrm{toBase}$ equals $D.\mathrm{toBase}$, and assume $\psi$ is a homomorphism for the relative group law attached to $h$ by the group-theoretic version of the fibrewise-algebraic-triviality cut: for every $s\colon T\to\operatorname{Spec}R$ and all $T$-points $x,y$ of $D.P$ over $s$, the product $\mathrm{mul}_s(x,y)$ followed by $\psi$ equals $\mathrm{mul}_s$ of $x$ followed by $\psi$ and $y$ followed by $\psi$. Then there is a unique additive group homomorphism $e\colon J\to J$ such that for every $y\in J$, $\mathrm{pts}(e\,y)$ followed by the projection $D.P\times_R\operatorname{Spec}R'\to D.P$ equals $\mathrm{pts}(y)$ followed by that projection followed by $\psi$.
--
--   This is the step transferring an endomorphism of the scheme representing the rigidified, fibrewise algebraically trivial relative Picard functor — one that respects the relative group law — to an additive endomorphism of an abstract abelian group $J$ identified with the $R'$-points of the base change, the identification being pinned down by the comparison of Poincaré bundles. It is used in the construction of Hecke and Galois actions on the points of the Jacobian of $X_1$ in the modular-curve part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_mul_comp_of_baseChangeIso.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_mul_comp_of_baseChangeIso
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
    (ψ : SchemeHomOver D.toBase D.toBase)
    (hψmul : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)) :
    ∃! e : J →+ J, ∀ y : J,
      (pts (e y)).1 ≫ pullback.fst D.toBase (specMap R R') = ((pts y).1 ≫ pullback.fst D.toBase (specMap R R')) ≫ ψ.1 := by sorry
