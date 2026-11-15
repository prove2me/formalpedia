-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_normal_projective_of_one_lt_dimension
-- name    : AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_of_one_lt_dimension
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-14T18:56:21.358108+00:00
-- url     : https://prove2.me/theorems/7f8de6dc-dd09-4e97-b12f-db3410d5b0f3
-- title:
--   Regular projective alterations of normal higher-dimensional varieties
-- statement:
--   Let $K$ be an arbitrary field and $X$ an integral normal projective $K$-scheme of dimension strictly greater than one. A closed projective embedding compatible with the given structure morphism of $X$ is supplied. There exist an integral regular projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$a:Y\longrightarrow X$$
--   which is finite over a nonempty open subscheme of $X$. The projective embedding of $Y$ has structure morphism exactly the composite through $a$ and the original structure morphism of $X$.
--
--   Normality means that every local ring of $X$ is integrally closed, and regularity is required at every local ring of $Y$. There is no perfectness or algebraic closedness hypothesis on $K$, and no smoothness assertion over $K$. The normal higher-dimensional alteration construction is the remaining input after finite normalization and the curve base cases.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1 and Section 4.3, p. 66; the normalization reduction in Section 4.10, p. 67; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Specialize the boundary subset to be empty and the target to be normal, projective and of dimension greater than one. Retain the arbitrary-field regular projective alteration, proper surjectivity, the nonempty finite locus and the exact structure morphism. The separate finite-normalization reduction is proved without an algebraic closedness or perfectness hypothesis. This normal-target construction remains Open.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_of_one_lt_dimension
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by sorry
