-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_projective_cover_family_of_isProper
-- name    : AlgebraicGeometry.Scheme.exists_finite_projective_cover_family_of_isProper
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-23T23:16:16.100397+00:00
-- url     : https://prove2.me/theorems/7122c49d-7892-48d9-993b-c22f041025df
-- title:
--   Finite projective cover family for a proper scheme over an affine base
-- statement:
--   Let $f\colon X\to\operatorname{Spec}R$ be proper. There are finitely many proper morphisms $Y_i\to X$ whose images cover $X$ and whose sources are projective over $R$ via the composite with $f$. The assertion gives actual closed embeddings into projective spaces and the equality of the two structure maps.
-- source:
--   Stacks Project, Chow's lemma, https://stacks.math.columbia.edu/tag/0815.

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.exists_finite_projective_cover_family_of_isProper (R : Type u) [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (I : Type u) (_ : Finite I) (Y : I → Scheme.{u}) (p : ∀ i, Y i ⟶ X)
      (n : I → ℕ) (j : ∀ i, Y i ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) R)),
      (∀ i, IsProper (p i) ∧ IsClosedImmersion (j i) ∧
        j i ≫ ProjSpace.π R (n i) = p i ≫ f) ∧
      ∀ x : X, ∃ (i : I) (y : Y i), p i y = x := by sorry
