-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/a30c67b8-21f7-5377-8026-4442bc0d67f5
-- title:
--   Finite étale descent of the represented relative Pic⁰
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a scheme over $R$ and $\varepsilon$ an element of `SchemeHomOver (𝟙 _) c`, i.e. a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ$-composition with $c$ the identity. Assume `hH0`: for every commutative $R$-algebra $A$, the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ coming from the second projection is bijective. Let $R'$ be an $R$-algebra that is module-finite, étale and faithfully flat over $R$. Let $D'$ consist of a scheme $D'.P$, a morphism $D'.\mathrm{toBase}\colon D'.P\to\operatorname{Spec}R'$ and a section of it, and let $h'$ witness that $D'$ represents the `algEquivZeroCut` subfunctor — rigidified line bundles on $C\times_R\operatorname{Spec}R'$ with its induced section satisfying `FibrewiseAlgEquivZero` — by a Poincaré bundle with that property, a universal property for all $R'$-schemes, and triviality of its pullback along the zero section. Assume $D'.\mathrm{toBase}$ is smooth, separated, quasi-compact and geometrically connected, and assume every point $x$ of $D'.P$ has an affine open $W$ containing the image under the descent action attached to the restriction of the representability along $\operatorname{Spec}R'\to\operatorname{Spec}R$ of every point of $(D'.P\times_{\operatorname{Spec}R}\operatorname{Spec}R')$ lying over $x$ in the first projection. Then there is such a designation $D$ over $R$ representing the corresponding cut for $(c,\varepsilon)$, with $D.\mathrm{toBase}$ smooth, separated, quasi-compact and geometrically connected, together with an isomorphism $D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'\cong D'.P$ compatible with the projections to $\operatorname{Spec}R'$.
--
--   This is the finite étale descent step for the relative $\mathrm{Pic}^0$ of a curve with a section: representability over $R'$, plus the orbit-wise affineness needed for effectivity of descent, yields representability over $R$ with the same geometric properties of the structure morphism. It is used in the constructions of relative $\mathrm{Pic}^0$ designations for base changes away from a finite set of primes in the degeneration analysis of the curves in play.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_DescentAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D')
    (hsm : Smooth D'.toBase) (hsep : IsSeparated D'.toBase) (hqc : QuasiCompact D'.toBase)
    (hgc : GeometricallyConnected D'.toBase)
    (haff : ∀ x : D'.P, ∃ W : D'.P.Opens, IsAffineOpen W ∧
      ∀ r : ↑(pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')),
        (pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')) r = x →
        (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act r ∈ W) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧ GeometricallyConnected D.toBase ∧
        ∃ e : pullback D.toBase (SmoothProperCurve.specMap R R') ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd D.toBase (SmoothProperCurve.specMap R R') := by sorry
