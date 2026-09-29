-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/386a5ed9-ac33-51c8-a0a7-d7ae25bc06da
-- title:
--   Representability of the Pic⁰ cut is Zariski-local on the base
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c : C \to \operatorname{Spec} R$ a morphism, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Two hypotheses are imposed. First, cohomological triviality in degree $0$ universally: for every $R$-algebra $A$, the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$, taken with respect to the algebra structure induced by the base-changed structure morphism, is bijective. Second, local representability: for every prime $\mathfrak p$ of $R$ there are $f \in R \setminus \mathfrak p$ and a pointed $R_f$-scheme datum $D'$ (a scheme $P$ with a morphism $P \to \operatorname{Spec} R_f$ and a section of it) together with a representation of the $\mathrm{Pic}^0$ cut for the base-changed curve $C_{R_f} \to \operatorname{Spec} R_f$ and the base-changed section: a line bundle on $C_{R_f} \times P$ rigidified along the section, whose restriction to every fibre over an algebraically closed point of $P$ satisfies `IsAlgEquivZero`, such that every rigidified line bundle on $C_{R_f} \times T$ with this fibrewise property is induced, by a unique morphism $T \to P$ over $\operatorname{Spec} R_f$, from it, and whose pullback along the section of $D'$ is isomorphic to the unit bundle; moreover $P \to \operatorname{Spec} R_f$ is smooth, separated, quasi-compact, surjective and geometrically connected. The conclusion asserts the existence of such a datum $D$ over $R$ itself: a pointed $R$-scheme representing the same $\mathrm{Pic}^0$ cut for $(c,\varepsilon)$, with structure morphism smooth, separated, quasi-compact, surjective and geometrically connected.
--
--   This is the descent step making representability of the fibrewise-algebraically-equivalent-to-zero part of the rigidified relative Picard functor, together with the geometric properties of the representing object, a Zariski-local condition on the base, the rigidified Picard presheaf being a Zariski sheaf under the hypothesis $H^0 = \mathcal{O}$ universally. It is invoked by the constructions of relative $\mathrm{Pic}^0$ for curves presented through smooth loci and two-chart degenerations, which verify the local hypothesis prime by prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (hloc : ∀ 𝔭 : PrimeSpectrum R, ∃ (f : R) (_ : f ∉ 𝔭.asIdeal)
      (D' : RelativePic0Designation (Localization.Away f) (SmoothProperCurve.baseChange R c (Localization.Away f))),
      Nonempty (RepresentsRelSubPic (SmoothProperCurve.baseChange R c (Localization.Away f))
          (sectionBaseChange (Localization.Away f) ε)
          (algEquivZeroCut (SmoothProperCurve.baseChange R c (Localization.Away f))
            (sectionBaseChange (Localization.Away f) ε)) D') ∧
        Smooth D'.toBase ∧ IsSeparated D'.toBase ∧ QuasiCompact D'.toBase ∧
        Surjective D'.toBase ∧ GeometricallyConnected D'.toBase) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧
        Surjective D.toBase ∧ GeometricallyConnected D.toBase := by sorry
