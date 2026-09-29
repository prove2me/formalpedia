-- Prove2me | Theorems.Thm_CongruenceSubgroup_isCusp_infty_gamma1_mapGL
-- name    : CongruenceSubgroup.isCusp_infty_gamma1_mapGL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/8ac0db98-62c3-5e6d-8de3-2b0d99c808f2
-- title:
--   i∞ is a cusp of Γ₁(M) in GL₂(ℝ)
-- statement:
--   For every natural number $M$ the point at infinity of the one-point compactification, `OnePoint.infty`, is a cusp of the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained as the image of the congruence subgroup $\Gamma_1(M) \le \mathrm{SL}_2(\mathbb{Z})$ under `Matrix.SpecialLinearGroup.mapGL ℝ`, the homomorphism $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{GL}_2(\mathbb{R})$ given by entrywise inclusion of $\mathbb{Z}$ into $\mathbb{R}$. Here $\Gamma_1(M)$ is the group of integral matrices of determinant $1$ that are congruent to an upper triangular unipotent matrix modulo $M$, and `IsCusp` is Mathlib's notion of a cusp for a subgroup of $\mathrm{GL}_2(\mathbb{R})$ acting on the one-point compactification: there is an element of the subgroup which is parabolic and fixes the given point. There are no hypotheses; the assertion holds for all $M$, including the degenerate values $M = 0$ and $M = 1$, for which $\Gamma_1(M)$ is the full modular group up to the congruence condition being vacuous.
--
--   This is the standard fact that every congruence subgroup of level $M$ has $i\infty$ among its cusps, here recorded for $\Gamma_1(M)$ after passage to $\mathrm{GL}_2(\mathbb{R})$. It is used to show that a cusp form for $\Gamma_1(M)$ has vanishing constant term in its $q$-expansion, in [`CuspForm.qCoeff_zero_eq_zero_gamma1`](thm.html#CuspForm.qCoeff_zero_eq_zero_gamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_isCusp_infty_gamma1_mapGL.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CongruenceSubgroup.isCusp_infty_gamma1_mapGL (M : ℕ) :
    IsCusp OnePoint.infty (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 M)) := by sorry
