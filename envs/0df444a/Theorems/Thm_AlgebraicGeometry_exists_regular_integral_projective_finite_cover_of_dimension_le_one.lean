-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_regular_integral_projective_finite_cover_of_dimension_le_one
-- name    : AlgebraicGeometry.exists_regular_integral_projective_finite_cover_of_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-14T17:25:29.810209+00:00
-- url     : https://prove2.me/theorems/067bbafb-8515-4409-8f7f-4144ea566ece
-- title:
--   Finite regular projective covers of integral curves
-- statement:
--   Let $K$ be an arbitrary field, and let $X$ be an integral projective $K$-scheme of dimension at most one, with a specified closed immersion into projective space compatible with its structure morphism. There exist an integral regular projective $K$-scheme $Y$ and a finite surjective $K$-morphism
--   $$a:Y\longrightarrow X$$
--   with $\dim Y=\dim X$. A projective embedding of $Y$ is supplied, whose structure morphism is exactly the composite through $a$ and the original structure morphism of $X$.
--
--   Every local ring of $Y$ is regular. The statement covers points and curves over arbitrary fields, including imperfect fields; it does not assert smoothness over $K$. Finiteness of $a$ holds over all of $X$, so the map is in particular an alteration.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 4.3, p. 66, the dimension-one normalization case; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . The proof uses the existing finite normal integral projective cover theorem and the fact that a Noetherian integrally closed local domain of Krull dimension at most one is a regular local ring (a field or discrete valuation ring). Retain the arbitrary-field regularity conclusion and the actual projective embedding; smoothness over the original field is not claimed.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_regular_integral_projective_finite_cover_of_dimension_le_one
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsFinite a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by sorry
