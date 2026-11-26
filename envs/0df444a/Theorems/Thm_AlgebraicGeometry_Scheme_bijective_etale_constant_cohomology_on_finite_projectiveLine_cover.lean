-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_bijective_etale_constant_cohomology_on_finite_projectiveLine_cover
-- name    : AlgebraicGeometry.Scheme.bijective_etale_constant_cohomology_on_finite_projectiveLine_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-26T07:06:47.631706+00:00
-- url     : https://prove2.me/theorems/60dad928-d7fe-4f88-83f8-a4f92cd2e7c7
-- title:
--   Étale cohomology of finite constant coefficients on finite covers of the projective line
-- statement:
--   Let Y be finite over a relative projective line over an algebraically closed field. After extending that field to an algebraically closed field, canonical restriction in positive-degree abelian étale cohomology is bijective for a finite constant group annihilated by a prime.
-- source:
--   Stacks Project, Theorem 59.83.10(7), https://stacks.math.columbia.edu/tag/03SC.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.bijective_etale_constant_cohomology_on_finite_projectiveLine_cover
    (R L E : Type u) [CommRing R] [Field L] [IsAlgClosed L] [Field E] [IsAlgClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (_ : IsPullback r d v (ProjSpace.π R 1)) (j : T ⟶ Spec (.of E)) (a : T ⟶ P)
    (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    {Y : Scheme.{u}} (p : Y ⟶ P) [IsFinite p] (N : ℕ) (_ : N.Prime)
    (M : AddCommGrpCat.{u}) [Finite M] (_ : N • 𝟙 M = 0) (q : ℕ) :
    Function.Bijective (PhilipponEtalePrimeTorsionComparison.restrict (pullback.snd a p)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M) (q + 1)) := by sorry
