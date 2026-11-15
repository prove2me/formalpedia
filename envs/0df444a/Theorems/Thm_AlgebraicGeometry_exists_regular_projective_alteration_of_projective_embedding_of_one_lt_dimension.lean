-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_projective_embedding_of_one_lt_dimension
-- name    : AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding_of_one_lt_dimension
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-14T17:25:25.812202+00:00
-- url     : https://prove2.me/theorems/10f3aa04-829b-4a87-ba22-d4e91083d9fc
-- title:
--   Regular projective alterations in dimension greater than one
-- statement:
--   Let $K$ be an arbitrary field and let $X$ be an integral projective $K$-scheme of dimension strictly greater than one. A compatible closed projective embedding of $X$ is supplied. There exist an integral regular projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$a:Y\longrightarrow X$$
--   which is finite over a nonempty open subscheme of $X$. The projective embedding of $Y$ has structure morphism exactly the composite through $a$ and the original structure morphism of $X$.
--
--   There are no perfectness, algebraic closedness or normality hypotheses. Regularity is required at every local ring of $Y$, and is not replaced by smoothness. This is the positive-dimensional induction step beyond curves in the projective-target regular alteration theorem.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1 and Section 4.3, p. 66, with the projective-target reduction in Sections 4.6–4.7, pp. 66–67; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Take the boundary subset to be empty and restrict to projective targets of dimension greater than one. The lower-dimensional normalization cases are proved separately. This retains arbitrary fields, properness, surjectivity, a nonempty finite locus, regular local rings and the exact projective structure morphism. The higher-dimensional alteration construction remains Open.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding_of_one_lt_dimension
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by sorry
