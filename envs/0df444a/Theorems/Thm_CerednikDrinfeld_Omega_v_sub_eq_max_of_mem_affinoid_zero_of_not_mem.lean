-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
-- name    : CerednikDrinfeld.Omega.v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/71776a0a-4646-552a-b9cb-746b453bfcda
-- title:
--   Valuation of z-a for z in the level-zero affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, and let $K$ carry a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi_1$ be a pseudo-uniformiser for the pair $(K_0, K)$, that is, an element $\varpi_1.\varpi \in K_0$ whose image in $K$ satisfies $0 < v(\varpi_1.\varpi) < 1$ and such that for every nonzero $a \in K_0$ there is an $N \in \mathbb{N}$ with $v(\varpi_1.\varpi)^N \le v(a) \le v(\varpi_1.\varpi)^{-N}$. Let $z, a \in K$. Assume $z$ lies in the level-$0$ affinoid `affinoid ϖ₁ 0`, i.e. $v(z) \le 1$ and $1 \le v(z - t)$ for every $t \in K_0$ with $v(t) \le 1$ (the bounds $v(\varpi_1.\varpi)^{\pm 0}$ being $1$), and assume $a$ does not lie in that affinoid. Then $$v(z - a) = \max\bigl(1, v(a)\bigr).$$
--
--   The level-$0$ affinoid is the standard Gauss-point fibre in the Drinfeld upper half plane, and the assertion is that the distance from any of its points to a fixed point outside it does not depend on the point chosen. It is used to show that a function holomorphic and invertible on the level-$0$ affinoid has constant valuation there, via [`CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one`](thm.html#CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K) {z a : K} (hz : z ∈ affinoid ϖ₁ 0) (ha : a ∉ affinoid ϖ₁ 0) :
    Valued.v (z - a) = max 1 (Valued.v a) := by sorry
