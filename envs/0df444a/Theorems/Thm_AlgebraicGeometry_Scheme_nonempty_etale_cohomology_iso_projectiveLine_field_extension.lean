-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_projectiveLine_field_extension
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T03:28:34.655379+00:00
-- url     : https://prove2.me/theorems/ccbcecc4-33b1-4e61-aba3-7c2b566f0c09
-- title:
--   Higher étale cohomology of the projective line is invariant over separably closed extensions
-- statement:
--   Let $P$ be a relative projective line over a separably closed field $L$. After extending $L$ to another separably closed field, the positive-degree étale cohomology of an abelian sheaf annihilated by a prime $ℓ$ agrees with the cohomology of its inverse image.
-- source:
--   Stacks Project, Lemma 59.83.12, https://stacks.math.columbia.edu/tag/0A5E.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension
    (R L E : Type u) [CommRing R] [Field L] [IsSepClosed L] [Field E] [IsSepClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)) (_ : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    (N : ℕ) (_ : N.Prime) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (_ : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves a).obj F).H (q + 1))) := by sorry
