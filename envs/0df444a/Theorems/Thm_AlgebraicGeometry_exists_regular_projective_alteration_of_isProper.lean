-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_isProper
-- name    : AlgebraicGeometry.exists_regular_projective_alteration_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-08T05:05:21.536399+00:00
-- url     : https://prove2.me/theorems/7d39a727-42f1-44d8-bc6b-4a025bb1032d
-- title:
--   Regular projective alterations of proper integral varieties
-- statement:
--   Let $K$ be an arbitrary field and let $C$ be an integral proper $K$-scheme. There are an integral $K$-scheme $Y$ and a proper surjective morphism
--   $$f:Y\longrightarrow C$$
--   which is finite over a nonempty open subscheme of $C$, such that every local ring of $Y$ is regular and $Y$ admits a closed immersion into some $\mathbb P^m_K$. The composite of this immersion with the projective structure morphism is exactly the given composite $Y\to C\to\operatorname{Spec}K$.
--
--   This is the proper-target case of the regular alteration theorem, with the divisor assertion omitted. The field may be imperfect; regularity is the asserted conclusion.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1 and Remark 4.2, p. 66, and the definition of alteration in Section 2.20, p. 61: https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Specialize X to a proper integral variety and the prescribed closed subset to the empty set. Its alteration source is proper over K, so the dense open immersion into the regular projective compactification is an isomorphism. Retain properness, dominance and generic finiteness; omit the normal-crossings divisor conclusion. No smoothness over an imperfect field is asserted.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_regular_projective_alteration_of_isProper
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by sorry
