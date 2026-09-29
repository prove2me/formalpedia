-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/ce94c3ca-aad1-5ddc-a1a0-9c75e1a50e83
-- title:
--   Base change of a relative Pic⁰ representation
-- statement:
--   Let $R$ be a commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a scheme over $\operatorname{Spec}R$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Let $D$ be a relative $\mathrm{Pic}^0$ designation over $R$ for $c$: a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec}R$ together with a section $D.\mathrm{zeroSection}$ of it. Assume $h$ witnesses that $D$ represents the subfunctor of the rigidified Picard functor of $(c,\varepsilon)$ cut out by `algEquivZeroCut c ε`, whose condition on a rigidified line bundle $M$ over $t\colon T\to\operatorname{Spec}R$ is that for every algebraically closed field $k$ and every $\operatorname{Spec}k\to T$ the pullback of $M.L$ to the corresponding geometric fibre is algebraically equivalent to zero; thus $h$ supplies a rigidified invertible module $h.\mathrm{poincare}$ on $C\times_R D.P$ satisfying this condition, the universal property that every such $M$ over $t$ admits a unique morphism $g\colon T\to D.P$ over $\operatorname{Spec}R$ with $(h.\mathrm{poincare}.\mathrm{pullbackAlong}\,g).L\cong M.L$, and an isomorphism of the restriction along $D.\mathrm{zeroSection}$ with the unit module. Then for every $R$-algebra $R'$ there is a witness $h'$ that the base-changed designation $D.\mathrm{baseChange}\,R'$ (with underlying scheme $D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'$, second projection and the induced zero section) represents the corresponding condition for the base-changed curve $\mathrm{baseChange}\,R\,c\,R'$ with the section $\mathrm{sectionBaseChange}\,R'\,\varepsilon$, and moreover the module underlying $h'.\mathrm{poincare}$ is isomorphic to the module obtained by transporting, via `BaseChange.ofR`, the pullback of $h.\mathrm{poincare}$ along the first projection $D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to D.P$ regarded as a morphism over $\operatorname{Spec}R$.
--
--   This is the compatibility of the relative Picard functor, and of the relative Jacobian that represents its $\mathrm{Pic}^0$ part, with base change of the base ring, together with the statement that the Poincaré bundle of the base-changed representing object may be taken to be the pullback of the original Poincaré bundle. It is used throughout the construction and study of the Jacobian of a smooth proper curve over a base, for instance in passing from a representation over $R$ to one over a residue field or a completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ∃ h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'),
      Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L) := by sorry
