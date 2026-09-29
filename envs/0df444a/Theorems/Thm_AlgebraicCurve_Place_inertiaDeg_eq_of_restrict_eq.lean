-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq
-- name    : AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/2babbc8b-41e2-5c0f-acf6-9e3403240472
-- title:
--   Inertia degree is constant on a Galois fibre
-- statement:
--   Let $K$, $F'$ and $M$ be fields with $F'$ and $M$ algebras over $K$ and $M$ an algebra over $F'$, the three structures forming a scalar tower, and assume $M$ is finite-dimensional over $F'$ and $M/F'$ is Galois. Let $W$ and $W'$ be places of $M$ over $K$, that is, valuation subrings of $M$ that contain the image of $K$ under the structure map, are distinct from $M$ itself, and are principal ideal rings. The hypothesis is that $W$ and $W'$ have the same restriction to $F'$: the preimages of their valuation subrings under $\mathrm{algebraMap}\,F'\,M$, regarded as places of $F'$ over $K$, coincide. The conclusion is the equality of the two inertia degrees over $F'$, where the inertia degree of a place $w$ of $M$ over $F'$ is the dimension of the residue field of the local ring $w$ as a vector space over the residue field of the restricted place $w|_{F'}$; thus $f(W'|_{F'}) = f(W|_{F'})$ as natural numbers.
--
--   This is the classical constancy of the residue (inertia) degree among the places of $M$ lying over a fixed place of $F'$ when $M/F'$ is finite Galois. It feeds the fundamental identity relating the number of places in a fibre, the ramification indices and the inertia degrees, used in [`AlgebraicCurve.Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`](thm.html#AlgebraicCurve.Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg) and in the two summation formulas over bifibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.FieldTheory.Galois.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' := by sorry
