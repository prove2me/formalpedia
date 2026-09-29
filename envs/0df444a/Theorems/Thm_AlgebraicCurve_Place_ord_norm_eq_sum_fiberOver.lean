-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
-- name    : AlgebraicCurve.Place.ord_norm_eq_sum_fiberOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/c32e65c8-953a-559a-9199-276c9be83549
-- title:
--   Valuation of a norm as a sum over the fibre
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, compatibly (a scalar tower $K \subseteq F \subseteq F'$), with $F'$ finite-dimensional and separable over $F$, and $F$ of characteristic zero. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and a principal ideal ring; to such a $v$ is attached the $\mathbb{Z}^{m0}$-valued adic valuation of the corresponding height-one point, and $v.\mathrm{ord}$ denotes minus the logarithm of that valuation, i.e. the associated normalised integer-valued order function. For a place $w$ of $F'$ over $K$, its restriction along $F \to F'$ is the place of $F$ whose valuation subring is the preimage of that of $w$, and the inertia degree $w.\mathrm{inertiaDeg}\,F$ is the degree of the residue field of $w$ over the residue field of that restriction. The fibre $v.\mathrm{fiberOver}\,F'$ is the (finite) set of places $w$ of $F'$ over $K$ whose restriction to $F$ is $v$. The assertion is that for every nonzero $f \in F'$, $$v.\mathrm{ord}\bigl(N_{F'/F}(f)\bigr) = \sum_{w \in v.\mathrm{fiberOver}\,F'} \bigl(w.\mathrm{inertiaDeg}\,F\bigr)\, w.\mathrm{ord}(f),$$ where $N_{F'/F}$ is the algebra norm of $F'$ over $F$.
--
--   This is the classical formula for the valuation of a field norm, $v(N_{F'/F}x) = \sum_{w \mid v} f(w\mid v)\, w(x)$, here in the form of an identity of integers for each place $v$ of $F$ over $K$. It is the place-by-place content of the compatibility of push-forward of divisors with the norm, and is used in the treatment of push-forward and pull-back of divisors on curves, for instance in [`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_of_decomposition`](thm.html#AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_of_decomposition) and [`AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber`](thm.html#AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_norm_eq_sum_fiberOver {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] (v : Place K F) {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by sorry
