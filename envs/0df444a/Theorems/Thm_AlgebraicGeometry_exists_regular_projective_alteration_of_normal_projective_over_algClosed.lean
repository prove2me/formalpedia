-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_normal_projective_over_algClosed
-- name    : AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_over_algClosed
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-14T20:23:29.565339+00:00
-- url     : https://prove2.me/theorems/1c7d8179-c830-44f7-ab85-4e79052497e9
-- title:
--   Regular projective alterations over algebraically closed fields
-- statement:
--   Let $K$ be an algebraically closed field and $X$ an integral normal projective $K$-scheme of dimension strictly greater than one. A closed projective embedding compatible with the given structure morphism of $X$ is supplied. There exist an integral regular projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$a:Y\longrightarrow X$$
--   which is finite over a nonempty open subscheme of $X$. The projective embedding of $Y$ has structure morphism exactly the composite through $a$ and the original structure morphism of $X$.
--
--   Normality and regularity are expressed at every local ring. The characteristic is unrestricted. This is the normal higher-dimensional geometric case remaining after finite normalization, the curve cases, and the proved descent from an algebraic closure.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1 and Sections 4.3–4.5, p. 66, with projective and normal reductions in Sections 4.7 and 4.10, p. 67; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Specialize the boundary subset to be empty and impose the normal projective higher-dimensional hypotheses and an algebraically closed field, as in the source’s reductions. Retain proper surjectivity, the nonempty finite locus, regular local rings, and exact projective structure morphism. The geometric alteration construction remains Open. A separate checked reduction preserves the full arbitrary-field theorem by constructing an integral closed dominating subscheme of the actual algebraic base change, normalizing it, and descending a smooth projective cover to a finite intermediate field.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_over_algClosed
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
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
