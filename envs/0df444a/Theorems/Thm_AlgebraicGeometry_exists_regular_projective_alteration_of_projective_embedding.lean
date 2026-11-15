-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_projective_embedding
-- name    : AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-14T16:40:22.059447+00:00
-- url     : https://prove2.me/theorems/90034818-17f8-42bd-bc45-40c554e3fed8
-- title:
--   Regular projective alterations of projective integral varieties
-- statement:
--   Let $K$ be an arbitrary field. Let $X$ be an integral $K$-scheme supplied with a closed immersion into a projective space over $K$, compatible with its given structure morphism. There exist an integral regular projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$a:Y\longrightarrow X$$
--   which is finite over some nonempty open subscheme of $X$. The projective embedding of $Y$ has structure morphism exactly the composite of $a$ with the original structure morphism of $X$.
--
--   There is no perfectness or algebraic closedness assumption on $K$, and no smoothness assertion. Regularity means that every local ring of $Y$ is regular. The specified projective embedding supplies properness and finite type of $X$; they are not separate hypotheses.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1, p. 66; projective-target reduction in Sections 4.6–4.7, pp. 66–67; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Specialize the closed subset to be empty and the target to be projective, retain the arbitrary-field regular projective alteration and its nonempty finite locus, and omit the normal-crossings boundary conclusion. For a proper target the alteration source is proper, so its dense open embedding into the projective compactification is an isomorphism. This theorem remains the explicit Open projective case; the separate proper-to-projective Chow reduction does not assume it proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by sorry
