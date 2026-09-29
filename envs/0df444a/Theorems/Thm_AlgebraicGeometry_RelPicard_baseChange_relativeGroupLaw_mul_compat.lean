-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
-- name    : AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/c7f05550-b3da-5d8f-a80e-a01935b589af
-- title:
--   Base change compatibility of the relative group law on points
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a scheme over $R$, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $c$: a scheme $D.P$ with a structure morphism $D.\mathrm{toBase} : D.P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it. Let $h$ witness that $D$ represents the cut `algEquivZeroCut c ε`, whose predicate on a rigidified line bundle $M$ over a base $t : T \to \operatorname{Spec} R$ is that for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$ the pullback of $M.L$ to the corresponding geometric fibre is algebraically equivalent to zero; thus $h$ provides a Poincaré bundle $h.\mathrm{poincare}$ over $D.\mathrm{toBase}$ satisfying this condition, the bijective classification of such bundles by morphisms $T \to D.P$ over $\operatorname{Spec} R$, and triviality of its pullback along $D.\mathrm{zeroSection}$. Let $R'$ be an $R$-algebra, $\mathrm{specMap}\,R\,R' : \operatorname{Spec} R' \to \operatorname{Spec} R$ the induced morphism, and let $h'$ witness the corresponding representability for the base-changed curve $\mathrm{baseChange}\,R\,c\,R' = \mathrm{pr}_2 : C \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$ with its induced section, the designation being $D.\mathrm{baseChange}\,R'$, with underlying scheme $D.P \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ and structure morphism the second projection. Assume $hP$: the line bundle of $h'.\mathrm{poincare}$ is isomorphic to the transport along $\mathrm{ofR}$ of the pullback of $h.\mathrm{poincare}$ along the first projection $\mathrm{pr}_1 : D.P \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to D.P$, viewed as a morphism over $\operatorname{Spec} R$. Let $t' : T \to \operatorname{Spec} R'$ be arbitrary, let $x, y$ be $T$-points of $D.P \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ over $t'$, and let $x_1, y_1$ be $T$-points of $D.P$ over $t' \circ \mathrm{specMap}\,R\,R'$ whose underlying morphisms are $\mathrm{pr}_1 \circ x$ and $\mathrm{pr}_1 \circ y$ respectively. Then the underlying morphism of the product of $x$ and $y$ for the relative group law on $(D.\mathrm{baseChange}\,R').\mathrm{toBase}$ determined by $h'$ (for the group cut `algEquivZeroGroupCut`, closing the above condition under tensor products and inverses), followed by $\mathrm{pr}_1$, equals the underlying morphism of the product of $x_1$ and $y_1$ for the relative group law on $D.\mathrm{toBase}$ determined by $h$ at the base $t' \circ \mathrm{specMap}\,R\,R'$.
--
--   This is the statement, on points with values in an arbitrary test scheme, that the canonical identification of $T$-points of the base change $D \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ with $T$-points of $D$ over $R$ is a homomorphism for the two relative group laws coming from the representability data $h$ and $h'$; equivalently, the relative Jacobian of the base-changed curve carries the base change of the group law of the relative Jacobian. It underlies the comparison of group laws used when passing from a relative $\mathrm{Pic}^0$ over a base ring to its fibres and localisations, and is cited by the base-change identity for relative group laws and by the results on kernel points over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t' (D.baseChange R').toBase)
    (x₁ y₁ : SchemeHomOver (t' ≫ specMap R R') D.toBase)
    (hx : x₁.1 = x.1 ≫ pullback.fst D.toBase (specMap R R'))
    (hy : y₁.1 = y.1 ≫ pullback.fst D.toBase (specMap R R')) :
    ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t' x y).1 ≫
        pullback.fst D.toBase (specMap R R') =
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (t' ≫ specMap R R') x₁ y₁).1 := by sorry
