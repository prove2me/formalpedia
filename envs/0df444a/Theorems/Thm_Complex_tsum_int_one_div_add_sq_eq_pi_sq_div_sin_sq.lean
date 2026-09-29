-- Prove2me | Theorems.Thm_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq
-- name    : Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/abd51774-6dcc-56c1-8794-8add1d1bf7d2
-- title:
--   Partial fraction expansion of π²/sin²(π z)
-- statement:
--   Let $z$ be a complex number lying in `Complex.integerComplement`, i.e. $z$ is not the image of any integer under the canonical map $\mathbb{Z}\to\mathbb{C}$. Then the unconditional sum over $n\in\mathbb{Z}$ of the terms $1/(z+n)^2$ equals $\pi^2/\sin(\pi z)^2$, where $\pi$ is the real number $\pi$ coerced into $\mathbb{C}$ and $\sin$ is the complex sine. The left-hand side is the `tsum` of the family $n \mapsto 1/(z+n)^2$ indexed by $\mathbb{Z}$; since $z$ avoids the integers no denominator vanishes, and the assertion of the equality with a nonzero right-hand side carries with it the summability of the family (an unconditionally summable family in $\mathbb{C}$, the sum being independent of any ordering of $\mathbb{Z}$). Equivalently, the statement is the classical identity $\sum_{n\in\mathbb{Z}} (z+n)^{-2} = \pi^2 \csc^2(\pi z)$ for all $z \in \mathbb{C}\setminus\mathbb{Z}$.
--
--   This is the weight-two partial fraction expansion, the term-by-term derivative of Euler's expansion $\pi\cot(\pi z) = z^{-1} + \sum_{n\ge 1}\bigl((z-n)^{-1}+(z+n)^{-1}\bigr)$, valid on the whole complement of $\mathbb{Z}$ and in particular at non-integral real arguments. It is used by [`ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq`](thm.html#ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq) to evaluate partial zeta values $\sum_{m \equiv t \ (N)} m^{-2}$ in closed form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

theorem Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 := by sorry
