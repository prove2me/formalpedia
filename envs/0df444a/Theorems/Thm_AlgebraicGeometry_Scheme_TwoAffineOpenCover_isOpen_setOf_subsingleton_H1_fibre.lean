-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/5e929bb3-629b-5d94-bd59-adf4a8c5d36a
-- title:
--   Openness of the vanishing locus of fibrewise check H¹
-- statement:
--   Let $A$ be a Noetherian commutative ring, let $C$ be a scheme and let $c \colon C \to \operatorname{Spec} A$ be a proper morphism. Let $\mathcal V$ be a two-chart affine open cover of $C$, that is, a pair of affine opens $U_0, U_1$ of $C$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine, and let $M$ be a sheaf of modules on $C$ satisfying `Scheme.Modules.IsInvertible`: every point of $C$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow C$ is isomorphic to the unit sheaf of modules on $U$. For a prime $\mathfrak p$ of $A$ with residue field $\kappa(\mathfrak p)$, form the fibre product of $c$ with $\operatorname{Spec} \kappa(\mathfrak p) \to \operatorname{Spec} A$, equipped with the cover by the preimages of $U_0$ and $U_1$ under the first projection and with the pullback of $M$ along that projection; the associated two-chart Čech datum has groups of sections over the two charts and their intersection, and its $H^1$ is the quotient of the sections over the intersection by the image of the difference of the two restriction maps. The assertion is that the set of primes $\mathfrak p \in \operatorname{Spec} A$ for which this $H^1$ is a subsingleton is open in $\operatorname{Spec} A$.
--
--   This is the openness statement needed to construct the charts of the relative Picard functor and of the Jacobian: since only the top-degree Čech group of a two-chart cover is involved, no general semicontinuity theorem is required. It is used by [`AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1`](thm.html#AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1) and by [`AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre
    {A : Type u} [CommRing A] [IsNoetherianRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c]
    (𝒱 : C.TwoAffineOpenCover) (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {𝔭 : PrimeSpectrum A | Subsingleton
      ((𝒱.pullback c 𝔭.asIdeal.ResidueField).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField)) ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj M)).H1} := by sorry
