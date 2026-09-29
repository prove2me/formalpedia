-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_self
-- name    : CerednikDrinfeld.Omega.crossRatio_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/14b71035-7597-51a5-a82e-b0f749a2e7eb
-- title:
--   Cross ratio equals 1 at a coincident pair
-- statement:
--   Let $K$ be a field and let $z, x, y \in K$ be elements with $z \neq x$ and $z \neq y$. The project's cross ratio is the function $\mathrm{crossRatio}(z, z_0, x, y) = \dfrac{(z-x)(z_0-y)}{(z-y)(z_0-x)}$ of four elements of $K$, formed with field division. The assertion is that specialising the second argument to the first gives $$\mathrm{crossRatio}(z, z, x, y) = \frac{(z-x)(z-y)}{(z-y)(z-x)} = 1 .$$ Both inequalities are genuinely needed: Lean's division sends $a/0$ to $0$, so if $z = x$ or $z = y$ the denominator $(z-y)(z-x)$ vanishes and the value of the expression is $0$ rather than $1$. No hypothesis on the characteristic of $K$ or on the relation between $x$ and $y$ is imposed; in particular $x = y$ is allowed.
--
--   This is the normalisation of the cross ratio at a coincident pair of arguments, i.e. the statement that the theta-type product built from cross ratios takes the value $1$ when its two point arguments agree. It is used in the Čerednik–Drinfeld chapter on the $p$-adic upper half plane, in particular for [`CerednikDrinfeld.Omega.theta_self_eq_one`](thm.html#CerednikDrinfeld.Omega.theta_self_eq_one) and for the valuation estimate [`CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius`](thm.html#CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_self.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_self
    {K : Type*} [Field K] (z x y : K) (hzx : z ≠ x) (hzy : z ≠ y) :
    crossRatio z z x y = 1 := by sorry
