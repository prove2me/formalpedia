-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback
-- name    : AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a92d50a0-a73a-534f-872a-d59eba9663c0
-- title:
--   Quotients by finite locally free equivalence relations base-change
-- statement:
--   Let $X, R, Y, X', R', Y'$ be schemes, let $s, t \colon R \to X$ and $p \colon X \to Y$ be morphisms with $p$ finite, flat, locally of finite presentation and surjective, and assume the square with $s, t$ over $p, p$ is cartesian, i.e. $(s,t)$ exhibits $R$ as $X \times_Y X$ so that $R$ is the kernel pair of $p$. Let $g \colon Y' \to Y$ be an arbitrary morphism, and let $p' \colon X' \to Y'$, $g_X \colon X' \to X$ form a cartesian square with $p$ and $g$, so that $X' = X \times_Y Y'$. Let $s', t' \colon R' \to X'$ and $g_R \colon R' \to R$ be such that $g_R, s'$ over $s, g_X$ form a cartesian square, and such that $g_R$ followed by $t$ equals $t'$ followed by $g_X$; assume finally $s'$ followed by $p'$ equals $t'$ followed by $p'$. Then the conjunction holds: $p'$ is finite, flat, locally of finite presentation and surjective; the square with $s', t'$ over $p', p'$ is cartesian, so $R' = X' \times_{Y'} X'$; and the cofork on $s', t'$ with projection $p'$ is a colimit, i.e. $p'$ is a coequaliser of $(s', t')$ in the category of schemes.
--
--   This is the statement that the quotient of a scheme by an effective finite locally free equivalence relation, characterised by '$p$ finite flat locally of finite presentation and surjective with $R = X\times_Y X$', commutes with arbitrary base change on the quotient, no flatness being required of $g$. It is used in the construction of quotient schemes and of relative group laws on them, being cited in the production of affine invariant neighbourhoods, in the gluing of local quotients to a global one, and in the transport of a relative group law across a quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback
    {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by sorry
