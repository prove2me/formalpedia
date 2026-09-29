-- Prove2me | Theorems.Thm_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
-- name    : AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/69e11075-36c4-50d8-beda-70782017d9c5
-- title:
--   Separatedness from a two-chart cover with closed intersection graph
-- statement:
--   Let $S, Y', A, B, U$ be schemes and $f' : Y' \to S$ a morphism. Let $j_A : A \to Y'$ and $j_B : B \to Y'$ be open immersions whose images cover $Y'$, in the sense that the union of the ranges of the underlying continuous maps of $j_A$ and $j_B$ is all of the space of $Y'$. Let $f_A : A \to S$ and $f_B : B \to S$ be morphisms with $j_A$ followed by $f'$ equal to $f_A$ and $j_B$ followed by $f'$ equal to $f_B$, and assume that both $f_A$ and $f_B$ are separated, i.e. their diagonals are closed immersions. Let $u_A : U \to A$ and $u_B : U \to B$ be morphisms forming a pullback square with $j_A$ and $j_B$ (so that $U$ realises the intersection $A \cap B$ inside $Y'$), and assume that the morphism $U \to A \times_S B$ induced by $u_A$ and $u_B$ — legitimate because $u_A$ followed by $f_A$ equals $u_B$ followed by $f_B$ — is a closed immersion. Then $f'$ is separated.
--
--   This is the standard criterion for separatedness of a morphism obtained by gluing two separated pieces along a common open subscheme, the gluing being separated exactly when the intersection embeds as a closed subscheme of the fibre product of the two pieces. It is used in the construction of models with prescribed open charts, where a model of a curve is assembled from two affine charts and has to be shown separated over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
    {S Y' A B U : Scheme.{u}} (f' : Y' ⟶ S)
    (jA : A ⟶ Y') (jB : B ⟶ Y') [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : Set.range jA.base ∪ Set.range jB.base = Set.univ)
    (fA : A ⟶ S) (fB : B ⟶ S) (hA : jA ≫ f' = fA) (hB : jB ≫ f' = fB) [IsSeparated fA] [IsSeparated fB]
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion
      (pullback.lift uA uB (by rw [← hA, ← hB, ← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback fA fB)) :
    IsSeparated f' := by sorry
