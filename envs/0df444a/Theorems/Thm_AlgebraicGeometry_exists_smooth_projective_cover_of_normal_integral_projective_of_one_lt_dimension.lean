-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_normal_integral_projective_of_one_lt_dimension
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_normal_integral_projective_of_one_lt_dimension
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-23T16:30:42.495718+00:00
-- url     : https://prove2.me/theorems/d0469dc1-ec46-4e82-ba15-d6bff3f539b1
-- title:
--   Smooth projective cover of a normal integral projective variety in dimension greater than one
-- statement:
--   Let $K$ be algebraically closed. Let $X$ be an integral proper $K$-scheme of dimension greater than one, equipped with a closed immersion into projective space and such that every local ring is integrally closed. There exist an integral smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism $f:Y\to X$. The projectivity of $Y$ is exhibited by a closed immersion into an actual projective space with the stated compatibility over $K$.
--
--   This is the normal projective case of the regular-alteration theorem. No characteristic restriction is imposed. Generic finiteness and normal-crossing boundary assertions are omitted. **Formalization Note.** The parent reduction proves the finite normal projective cover and preserves dimension, so normality is a hypothesis of this remaining geometric case rather than an extra assumption on the original target.
-- source:
--   Derived specialization of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathematiques de l IHES 83 (1996), Theorem 4.1 and Remark 4.2, p.66, and Section 4.10, p.67 (normality reduction); https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Over the algebraically closed field, regular finite-type schemes are smooth, and properness makes the regular projective compactification equal to the alteration source. This is a derived consequence, not a transcription of the full theorem.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_normal_integral_projective_of_one_lt_dimension
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by sorry
