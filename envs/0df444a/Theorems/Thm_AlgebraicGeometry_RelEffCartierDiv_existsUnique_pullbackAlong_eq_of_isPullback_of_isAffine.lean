-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
-- name    : AlgebraicGeometry.RelEffCartierDiv.existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/560eadc7-4fe3-54c7-a1a8-753a99332ba5
-- title:
--   Descent of relative effective Cartier divisors along finite flat covers
-- statement:
--   Let $\mathcal{C}$ and $S$ be affine schemes, $f \colon \mathcal{C} \to S$ a morphism, $r$ a natural number, and let $X, Y, R$ be schemes with $X$ and $Y$ affine, equipped with morphisms $g_X \colon X \to S$, $g_Y \colon Y \to S$, $g_R \colon R \to S$. Let $p \colon X \to Y$ satisfy $g_Y \circ p = g_X$ and be finite, flat, locally of finite presentation and surjective, and let $s, t \colon R \to X$ satisfy $g_X \circ s = g_R$, $g_X \circ t = g_R$ and make the square with $s, t$ over $p, p$ a pullback square, so that $R$ together with $s$ and $t$ is the kernel pair $X \times_Y X$. Let $D$ be a relative effective Cartier divisor of degree $r$ for $f$ over $g_X$, that is: an ideal sheaf datum $D.I$ on $\mathcal{C} \times_S X$ whose associated closed immersion, followed by the projection to $X$, is finite, flat and locally of finite presentation and has fibre rank $r$ at every point of $X$. Assume $D$ is invariant, $s^{*}D = t^{*}D$, where pullback along an $S$-morphism $\varphi$ is taken by comapping the ideal sheaf datum along the induced map $\mathcal{C} \times_S T \to \mathcal{C} \times_S T'$. Then there is exactly one relative effective Cartier divisor $D_Y$ of degree $r$ for $f$ over $g_Y$ with $p^{*}D_Y = D$.
--
--   This is faithfully flat descent for relative effective Cartier divisors along a finite flat surjective cover, in the case where the base, the total space and the covering schemes are affine, so that it reduces to descent of ideals along a faithfully flat ring extension. It is the affine input to [`AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine), used in the construction of the universal divisor on a symmetric power quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine.lean

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
    {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] {f : 𝒞 ⟶ S} {r : ℕ}
    {X Y R : Scheme.{u}} [IsAffine X] [IsAffine Y] {gX : X ⟶ S} {gY : Y ⟶ S} {gR : R ⟶ S}
    (p : X ⟶ Y) (hp : p ≫ gY = gX)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (s t : R ⟶ X) (hs : s ≫ gX = gR) (ht : t ≫ gX = gR) (hR : IsPullback s t p p)
    (D : RelEffCartierDiv f r gX) (hD : D.pullbackAlong s hs = D.pullbackAlong t ht) :
    ∃! DY : RelEffCartierDiv f r gY, DY.pullbackAlong p hp = D := by sorry
