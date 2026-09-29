-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_swap
-- name    : CerednikDrinfeld.Omega.crossRatio_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/795b8d73-4882-512e-a73e-7ac1fde7f015
-- title:
--   Cross ratio is invariant under exchanging the two pairs
-- statement:
--   Let $K$ be a field and let $z, z_0, x, y$ be four elements of $K$ (no distinctness or non-vanishing hypotheses are imposed). The project's cross ratio is defined by $$\mathrm{crossRatio}(z,z_0,x,y) = \frac{(z-x)(z_0-y)}{(z-y)(z_0-x)},$$ division being Lean's field division, so that the value is $0$ when the denominator $(z-y)(z_0-x)$ vanishes. The theorem asserts the identity $$\mathrm{crossRatio}(z,z_0,x,y) = \mathrm{crossRatio}(x,y,z,z_0),$$ that is, $$\frac{(z-x)(z_0-y)}{(z-y)(z_0-x)} = \frac{(x-z)(y-z_0)}{(x-z_0)(y-z)}.$$ The assertion is unconditional: since the numerator and the denominator of the right-hand side are each obtained from those of the left-hand side by two sign changes, the two quotients have literally equal numerators and equal denominators, and the equality therefore also holds in the degenerate cases where the denominator is zero.
--
--   This is the standard symmetry of the cross ratio under interchanging the pair $(z,z_0)$ of arguments with the pair $(x,y)$. In the Cerednik–Drinfeld material on the Drinfeld upper half plane it feeds into the symmetry of the theta products built from cross ratios, and it is used in [`CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_swap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_swap
    {K : Type*} [Field K] (z z₀ x y : K) :
    crossRatio z z₀ x y = crossRatio x y z z₀ := by sorry
