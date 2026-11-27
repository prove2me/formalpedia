-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_bijective_etale_cyclic_cohomology_prime_to_characteristic_on_finite_projectiveLine_cover
-- name    : AlgebraicGeometry.Scheme.bijective_etale_cyclic_cohomology_prime_to_characteristic_on_finite_projectiveLine_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-27T04:27:46.887941+00:00
-- url     : https://prove2.me/theorems/b28ef6d6-3cab-4483-a20e-e30d18a79bc3
-- title:
--   Étale comparison for cyclic prime-to-characteristic coefficients on a finite cover of the projective line
-- statement:
--   Canonical restriction under extension of algebraically closed fields is bijective in positive-degree étale cohomology of a finite cover of a projective line with constant cyclic coefficients of prime order invertible in the field.
-- source:
--   Stacks Project, Theorem 59.83.10(6), https://stacks.math.columbia.edu/tag/03SC.

import Mathlib.Algebra.Field.ZMod
import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.bijective_etale_cyclic_cohomology_prime_to_characteristic_on_finite_projectiveLine_cover
    (R L E : Type u) [CommRing R] [Field L] [IsAlgClosed L] [Field E] [IsAlgClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (_ : IsPullback r d v (ProjSpace.π R 1)) (j : T ⟶ Spec (.of E)) (a : T ⟶ P)
    (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    {Y : Scheme.{u}} (p : Y ⟶ P) [IsFinite p] (N : ℕ) (_ : N.Prime)
    (_ : (N : L) ≠ 0) (q : ℕ) :
    Function.Bijective (PhilipponEtalePrimeTorsionComparison.restrict (pullback.snd a p)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod N)))) (q + 1)) := by sorry
