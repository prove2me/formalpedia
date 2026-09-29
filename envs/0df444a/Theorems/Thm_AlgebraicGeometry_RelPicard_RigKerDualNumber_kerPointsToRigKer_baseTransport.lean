-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport
-- name    : AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/4d9e17fe-0670-528d-a785-ef5f510c4d7c
-- title:
--   Base transport commutes with dual-number points of Pic⁰
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes and $\varepsilon$ a section of $c$, that is a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ c$ (diagrammatically $\varepsilon\ {\gg}\ c$) the identity. Let $D$ consist of a scheme $P$ with structure morphism $D.\mathrm{toBase}\colon P\to\operatorname{Spec}R$ and a zero section, and let $h$ be representing data for the $\varepsilon$-rigidified relative Picard functor cut out by `algEquivZeroCut`, whose condition on a rigidified line bundle $M$ over $t\colon T\to\operatorname{Spec}R$ asks that for every algebraically closed field $k$ and every $k$-point of $T$ the pullback of $M.L$ to the corresponding fibre of $c$ be algebraically equivalent to zero; thus $h$ provides a Poincaré bundle $h.\mathrm{poincare}$ on $C\times_R P$ satisfying the cut, a unique classifying morphism for every bundle satisfying the cut, and triviality along the zero section. Let $R'$ be an $R$-algebra and let $h'$ be such representing data for the base-changed curve $\operatorname{pr}_2\colon C\times_R R'\to\operatorname{Spec}R'$ with the induced section `sectionBaseChange`, for the designation $D.\mathrm{baseChange}\,R'$ given by $P\times_R\operatorname{Spec}R'$ with second projection and the induced zero section. Assume $h'.\mathrm{poincare}.L$ is isomorphic to the line bundle obtained by applying the base-change transport `BaseChange.ofR` to the pullback of $h.\mathrm{poincare}$ along the first projection $P\times_R\operatorname{Spec}R'\to P$. Let $B$ be an $R'$-algebra, an $R$-algebra, the two structures forming a scalar tower. Let $x$ be a morphism $\operatorname{Spec}B[\epsilon]\to P$ over $\operatorname{Spec}R$ whose composite with the reduction $\operatorname{Spec}B\to\operatorname{Spec}B[\epsilon]$ is the unit point of the relative group law on $D.\mathrm{toBase}$ attached to $h$ via `algEquivZeroGroupCut`, and let $x'$ be the analogous morphism $\operatorname{Spec}B[\epsilon]\to P\times_R\operatorname{Spec}R'$ over $\operatorname{Spec}R'$ relative to $h'$, with $x'$ followed by the first projection equal to $x$. Then the base-transport bijection `RigKerDualNumber.baseTransport` sends the class of $x^{*}h.\mathrm{poincare}$, that is $h.\mathrm{kerPointsToRigKer}\,B\,x$, to $h'.\mathrm{kerPointsToRigKer}\,B\,x'$.
--
--   This is the base-change compatibility of the identification of the kernel of $\operatorname{Pic}(B[\epsilon])\to\operatorname{Pic}(B)$ with the dual-number points of the representing scheme lying above the unit section, obtained by pulling back the Poincaré bundle. It is used in the analysis of deformation classes and their Čech description of $H^1$ for the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (x : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber B)) D.toBase //
      dualNumberReduction R B ≫ x.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R B)).1 })
    (x' : { x' : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (D.baseChange R').toBase //
      dualNumberReduction R' B ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
          (Scheme.TwoAffineOpenCover.specMap R' B)).1 })
    (hxx' : x'.1.1 ≫ pullback.fst D.toBase (specMap R R') = x.1.1) :
    RigKerDualNumber.baseTransport R' c ε B (h.kerPointsToRigKer B x) = h'.kerPointsToRigKer B x' := by sorry
