-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_projectiveLine_field_extension_of_isAlgClosed
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension_of_isAlgClosed
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T04:01:16.431807+00:00
-- url     : https://prove2.me/theorems/19504c34-5333-4777-ab6b-cc242a7547d8
-- title:
--   Higher étale cohomology of the projective line over algebraically closed extensions
-- statement:
--   After an extension of algebraically closed fields, positive-degree étale cohomology of a relative projective line with abelian sheaf coefficients killed by a prime agrees with the cohomology of the inverse-image sheaf.
-- source:
--   Stacks Project, Theorem 59.83.10(7), https://stacks.math.columbia.edu/tag/03SC.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension_of_isAlgClosed
    (R L E : Type u) [CommRing R] [Field L] [IsAlgClosed L] [Field E] [IsAlgClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)) (_ : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    (N : ℕ) (_ : N.Prime) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (_ : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves a).obj F).H (q + 1))) := by sorry
