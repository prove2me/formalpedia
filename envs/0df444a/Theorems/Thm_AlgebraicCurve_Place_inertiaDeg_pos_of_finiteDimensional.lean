-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
-- name    : AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/544f298e-a487-51ba-87ff-8c1c72d2b416
-- title:
--   Positivity of the inertia degree in a finite extension
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, and assume $F'$ is finite-dimensional over $F$. Let $w$ be a place of $F'$ over $K$ in the sense of the project, that is a valuation subring $\mathcal{O}_w \subseteq F'$ containing the image of $K$ under the structure map, different from all of $F'$, and whose underlying ring is a principal ideal ring. Its restriction $w|_F$ is the place of $F$ over $K$ whose valuation subring is the preimage $\mathcal{O}_w \cap F$ of $\mathcal{O}_w$ under the structure map $F \to F'$, and the inertia degree $f(w/w|_F)$ is defined as the $\mathrm{Module.finrank}$ of the residue field $\mathcal{O}_w/\mathfrak{m}_w$ of $w$ regarded as a module over the residue field of $w|_F$. The assertion is that this natural number is strictly positive. Since `Module.finrank` takes the value $0$ on modules that are not finitely generated free of finite rank, the content is that the residue extension $\kappa(w)/\kappa(w|_F)$ is finite-dimensional; no separability hypothesis is imposed.
--
--   This is the residue-degree half of the fundamental inequality for places in a finite extension of fields: the residue field of $w$ is finite over that of its restriction, so the inertia degree is not the junk value $0$. Together with the tower formula relating the degree of $w$ to $f(w/w|_F)$ and the degree of $w|_F$, it is used in the divisor theory of curves over $K$, for instance by [`AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin`](thm.html#AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin) and [`AlgebraicCurve.Place.eq_of_finrank_lt_two_mul_ramificationIndex`](thm.html#AlgebraicCurve.Place.eq_of_finrank_lt_two_mul_ramificationIndex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] (w : Place K F') : 0 < w.inertiaDeg F := by sorry
