-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback
-- name    : AlgebraicGeometry.exists_fin_eq_of_isClosedImmersion_of_finite_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0c365fb8-494b-5e87-bcdc-fd87241784ac
-- title:
--   Finite enumeration of coincidences with a closed immersion
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in a fixed universe), let $i_1 \colon Y \to X$ be a morphism of schemes and let $i_2 \colon Z \to X$ be a closed immersion, and assume that the underlying topological space of the fibre product $Y \times_X Z$ is finite. The assertion is that there exist a natural number $n$ and families of points $y \colon \mathrm{Fin}\,n \to Y$ and $z \colon \mathrm{Fin}\,n \to Z$ (points of the underlying spaces) such that: the map $r \mapsto y_r$ is injective; for every index $r$ the two points have the same image in $X$, that is $i_1(y_r) = i_2(z_r)$ on underlying spaces; and every coincidence is on the list, i.e. for all $P \in Y$ and $Q \in Z$ with $i_1(P) = i_2(Q)$ there is an index $r$ with $P = y_r$ and $Q = z_r$. Note that the list is not asserted to be injective in the second coordinate, nor minimal; injectivity is claimed only for $r \mapsto y_r$.
--
--   This is bookkeeping on the underlying set of a fibre product of schemes: it converts the finiteness of $Y \times_X Z$ into an explicit finite enumeration of the pairs of points of $Y$ and $Z$ having a common image in $X$. It is used in the analysis of Deligne–Rapoport models, where the finitely many crossings of two components (for instance two projective lines meeting in a degenerate fibre) must be listed, in [`ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth`](thm.html#ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth) and its variant with an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fin_eq_of_isClosedImmersion_of_finite_pullback
    {X Y Z : Scheme.{u}} (i₁ : Y ⟶ X) (i₂ : Z ⟶ X) [IsClosedImmersion i₂]
    [Finite ↥(pullback i₁ i₂)] :
    ∃ (n : ℕ) (y : Fin n → Y) (z : Fin n → Z), Function.Injective y ∧
      (∀ r, i₁.base (y r) = i₂.base (z r)) ∧
      ∀ (P : Y) (Q : Z), i₁.base P = i₂.base Q → ∃ r, P = y r ∧ Q = z r := by sorry
