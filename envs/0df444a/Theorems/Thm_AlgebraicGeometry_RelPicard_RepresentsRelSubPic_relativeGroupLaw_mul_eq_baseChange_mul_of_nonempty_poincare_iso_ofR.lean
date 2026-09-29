-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/e0965224-007b-5af1-88cb-cdd4c77f042b
-- title:
--   Base-changed Pic⁰ datum carries the base-changed group law
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity). Let $D$ consist of a scheme $P$ with a structure morphism $P\to\operatorname{Spec}R$ and a section of it, and let $h$ be a representing datum for the cut `algEquivZeroCut c ε`: a line bundle on $C\times_{\operatorname{Spec}R}P$ rigidified along $\varepsilon$, whose restriction to every geometric fibre is algebraically equivalent to zero, which is trivial along the zero section and which classifies, uniquely up to a unique morphism over $\operatorname{Spec}R$, every such fibrewise algebraically trivial rigidified bundle on every base $T\to\operatorname{Spec}R$. Let $R'$ be an $R$-algebra and $h'$ a representing datum of the same kind for $C\times_R\operatorname{Spec}R'$ with the base-changed section, on $P\times_R\operatorname{Spec}R'$ with its second projection and base-changed zero section. Assume the tie $h P$: the bundle underlying the Poincaré bundle of $h'$ is isomorphic to the transport along `BaseChange.ofR` of the pullback of the Poincaré bundle of $h$ along the first projection $P\times_R\operatorname{Spec}R'\to P$. Then for every scheme $T$, every $t'\colon T\to\operatorname{Spec}R'$ and all sections $x,y$ of $P\times_R\operatorname{Spec}R'$ over $t'$, the multiplication of the relative group law determined by $h'$ agrees with that of the base change along $\operatorname{Spec}R'\to\operatorname{Spec}R$ of the relative group law determined by $h$.
--
--   This is the compatibility of the group law on the relative $\mathrm{Pic}^0$ functor with base change: once the two Poincaré bundles are tied, the representing datum over $R'$ induces exactly the base change of the law over $R$. It is used in the construction of the Néron-model data attached to the Jacobian of a modular curve at a place, where a group law obtained after base change must be identified with the base change of the given one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (D.baseChange R').toBase),
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t' x y =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).baseChange (specMap R R')).mul t' x y := by sorry
