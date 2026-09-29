-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_eq_comp_of_mul_comp
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_eq_comp_of_mul_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d3d92533-f0d6-55f7-9edf-0ce5f8d73c79
-- title:
--   Group endomorphism of Pic⁰ induces unique additive endomorphism
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a morphism $c : C \to \operatorname{Spec} R$ and a section $\varepsilon$ of $c$ over the identity of $\operatorname{Spec} R$, and a designation $D$ of the relative $\mathrm{Pic}^0$, that is a scheme $D.P$ with a structure morphism $D.\mathrm{toBase} : D.P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it. Let $h$ witness `RepresentsRelSubPic c ε (algEquivZeroCut c ε) D`: a rigidified line bundle $h.\mathrm{poincare}$ on the base change of $c$ along $D.\mathrm{toBase}$ which is fibrewise algebraically equivalent to zero (after pullback along any $\operatorname{Spec} k \to D.P$ with $k$ algebraically closed), together with the universal property that every rigidified line bundle over $t : T \to \operatorname{Spec} R$ with this fibrewise property is, up to isomorphism of underlying bundles, the pullback of $h.\mathrm{poincare}$ along a unique $T$-point of $D.P$ over $t$, and with triviality of the pullback along the zero section. Let $J$ be an additive abelian group and $\mathrm{pts}$ a bijection from $J$ to the set of sections of $D.\mathrm{toBase}$ over $\operatorname{Spec} R$. Assume $\mathrm{pts}$ is additive in the bundle-theoretic sense: for all $a, b \in J$ there exists an isomorphism of the pullback of $h.\mathrm{poincare}$ along $\mathrm{pts}(a+b)$ with the tensor product of its pullbacks along $\mathrm{pts}(a)$ and $\mathrm{pts}(b)$. Let $\psi : D.P \to D.P$ satisfy $\psi \circ\,$(i.e. composed with) $D.\mathrm{toBase} = D.\mathrm{toBase}$, and assume $\psi$ is a homomorphism for the relative group law on $D.\mathrm{toBase}$ obtained from $h$ via the group cut `algEquivZeroGroupCut c ε`: for every $s : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ over $s$, the multiplication $\mathrm{mul}\,s\,x\,y$ followed by $\psi$ equals $\mathrm{mul}\,s$ applied to $x$ followed by $\psi$ and $y$ followed by $\psi$. Then there is a unique additive group homomorphism $e : J \to J$ such that for all $y \in J$ the underlying morphism of $\mathrm{pts}(e\,y)$ equals the underlying morphism of $\mathrm{pts}(y)$ followed by $\psi$.
--
--   This transfers an endomorphism of the representing scheme of the relative $\mathrm{Pic}^0$, assumed compatible with the relative group law, into an endomorphism of an abstract abelian group $J$ identified with the $R$-points of that scheme by a dictionary $\mathrm{pts}$; no base change is involved, the group $J$ and the scheme living over the same base. It is used in the construction of the special-fibre operator package for $X_1(p)$, where Hecke, diamond and descended operators on the Jacobians of the components are read off as additive endomorphisms of the corresponding point groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_eq_comp_of_mul_comp.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_eq_comp_of_mul_comp
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (J : Type u) [AddCommGroup J]
    (pts : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (hadd : ∀ a b : J, Nonempty
      ((h.poincare.pullbackAlong (pts (a + b))).L ≅
        (h.poincare.pullbackAlong (pts a)).L ⊗ (h.poincare.pullbackAlong (pts b)).L))
    (ψ : SchemeHomOver D.toBase D.toBase)
    (hψmul : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)) :
    ∃! e : J →+ J, ∀ y : J, (pts (e y)).1 = (pts y).1 ≫ ψ.1 := by sorry
