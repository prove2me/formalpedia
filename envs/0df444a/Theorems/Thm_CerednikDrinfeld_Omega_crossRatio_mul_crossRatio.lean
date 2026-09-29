-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio
-- name    : CerednikDrinfeld.Omega.crossRatio_mul_crossRatio
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b9878986-59fc-54b1-bb67-4cea97ad1b2d
-- title:
--   Cocycle identity for the cross ratio
-- statement:
--   Let $K$ be a field and let $z, w, z_0, x, y \in K$, and suppose $w \neq x$ and $w \neq y$. Writing, as in the project's definition, $$\mathrm{crossRatio}(z, z_0, x, y) \;=\; \frac{(z-x)(z_0-y)}{(z-y)(z_0-x)}$$ for the cross ratio of four field elements (a quotient formed with Lean's field division, so that the value is $0$ whenever the denominator $(z-y)(z_0-x)$ vanishes), the assertion is the multiplicative identity $$\mathrm{crossRatio}(z, w, x, y)\cdot \mathrm{crossRatio}(w, z_0, x, y) \;=\; \mathrm{crossRatio}(z, z_0, x, y),$$ that is, $$\frac{(z-x)(w-y)}{(z-y)(w-x)}\cdot\frac{(w-x)(z_0-y)}{(w-y)(z_0-x)} \;=\; \frac{(z-x)(z_0-y)}{(z-y)(z_0-x)}.$$ No hypotheses are imposed on $z$, $z_0$, $x$, $y$: with the convention that division by zero yields $0$, the identity holds in this generality, the only assumptions being the two needed to cancel the factor $(w-y)(w-x)$ occurring in the numerator and the denominator of the product.
--
--   The cross ratio in the middle variable satisfies a cocycle (telescoping) relation, which expresses the dependence of a cross-ratio product on its base point. It is used in the Čerednik–Drinfeld setting to compare theta products formed with different base points, and is cited by [`CerednikDrinfeld.Omega.theta_mul_theta_basePoint`](thm.html#CerednikDrinfeld.Omega.theta_mul_theta_basePoint), [`CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint`](thm.html#CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint) and [`CerednikDrinfeld.Omega.theta_pmoebius_eq_mul`](thm.html#CerednikDrinfeld.Omega.theta_pmoebius_eq_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_mul_crossRatio.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_mul_crossRatio
    {K : Type*} [Field K] (z w z₀ x y : K) (hwx : w ≠ x) (hwy : w ≠ y) :
    crossRatio z w x y * crossRatio w z₀ x y = crossRatio z z₀ x y := by sorry
