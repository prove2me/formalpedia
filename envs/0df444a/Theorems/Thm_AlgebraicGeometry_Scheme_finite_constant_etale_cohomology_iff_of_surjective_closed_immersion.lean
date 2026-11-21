-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_iff_of_surjective_closed_immersion
-- name    : AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_iff_of_surjective_closed_immersion
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T18:09:33.137653+00:00
-- url     : https://prove2.me/theorems/c22e889c-8853-44bc-8e5e-e61ed4e83966
-- title:
--   Étale finiteness is invariant under a surjective closed immersion
-- statement:
--   Let $i\colon Y\to X$ be a surjective closed immersion of schemes and $A$ an abelian group.
--   For any $q\geq 0$,
--   $$H^q_{\mathrm{et}}(X,\underline A)\text{ is finite}\quad\Longleftrightarrow\quad
--   H^q_{\mathrm{et}}(Y,\underline A)\text{ is finite},$$
--   with the constant coefficient sheaf on each small étale site. This is the finiteness
--   consequence of topological invariance for a thickening.
-- source:
--   Stacks Project, Proposition 59.45.4 (https://stacks.math.columbia.edu/tag/03SI), specialized to a surjective closed immersion and constant coefficients.

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_iff_of_surjective_closed_immersion
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [Surjective i]
    (A : Type u) [AddCommGroup A] (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) ↔ Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) := by sorry
