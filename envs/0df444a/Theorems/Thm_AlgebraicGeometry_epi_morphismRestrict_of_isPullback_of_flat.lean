-- Prove2me | Theorems.Thm_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat
-- name    : AlgebraicGeometry.epi_morphismRestrict_of_isPullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/72e76710-5997-55bd-aee0-5a14dc575ef9
-- title:
--   Zariski-local epimorphy of affine surjections under flat base change
-- statement:
--   Let $X, Y, X', Y'$ be schemes and let $p : X \to Y$ be a morphism that is affine (`IsAffineHom`) and surjective. Let $f : Y' \to Y$ be flat, and let $p' : X' \to Y'$, $q : X' \to X$ be morphisms forming a pullback square `IsPullback q p' p f`, that is, $q$ followed by $p$ equals $p'$ followed by $f$ and the resulting square exhibits $X'$ as the fibre product $X \times_Y Y'$ with projections $q$ and $p'$. Assume further that for every open subscheme $U$ of $Y$ the restricted morphism $p \mid_U : p^{-1}(U) \to U$ is an epimorphism in the category of schemes. Then for every open subscheme $U'$ of $Y'$ the restricted morphism $p' \mid_{U'} : p'^{-1}(U') \to U'$ is an epimorphism in the category of schemes. All schemes and morphisms are taken in the smallest universe.
--
--   The hypothesis that $p\mid_U$ is epi for every open $U$ is the scheme-theoretic form of schematic dominance, and the statement is its stability under flat base change for affine surjective morphisms, in the Zariski-local form needed later. It is used in the construction of base changes of tower quotient data, by [`AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback`](thm.html#AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback) and [`AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat_of_forall_exists_chart`](thm.html#AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat_of_forall_exists_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.epi_morphismRestrict_of_isPullback_of_flat
    {X Y X' Y' : Scheme.{0}} (p : X ⟶ Y) [IsAffineHom p] [Surjective p]
    (f : Y' ⟶ Y) [Flat f] (p' : X' ⟶ Y') (q : X' ⟶ X) (sq : IsPullback q p' p f)
    (hp : ∀ U : Y.Opens, Epi (p ∣_ U)) (U' : Y'.Opens) : Epi (p' ∣_ U') := by sorry
