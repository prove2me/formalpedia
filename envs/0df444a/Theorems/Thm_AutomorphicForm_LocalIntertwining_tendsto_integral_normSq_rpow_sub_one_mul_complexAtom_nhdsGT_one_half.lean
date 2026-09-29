-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
-- name    : AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/348936f5-f859-5685-8a65-2515fd334a90
-- title:
--   Vanishing of the twisted complex atom integral as σdownarrow 1/2
-- statement:
--   Let $c',d'$ be complex numbers, assumed not both zero, and let $a,b,m$ be natural numbers with $a+b\le m$. For a real parameter $\sigma$ consider the integral over $\mathbb{C}$, with respect to the standard two-dimensional Lebesgue measure, of the product of the real scalar $\bigl(\|c'z+d'\|^{2}\bigr)^{2\sigma-1}-1$ (a real power, viewed in $\mathbb{C}$) with the expression $z^{a}\,\overline{z}^{\,b}\,\bigl(1+\|z\|^{2}\bigr)^{-(2\sigma+1)-m/2}$, the last factor being a complex power of the real number $1+\|z\|^{2}$ with exponent $-(2\sigma+1)-m/2$ and $\overline{z}$ the complex conjugate. The assertion is that, as $\sigma$ tends to $1/2$ from the right (the filter of right-hand neighbourhoods of $1/2$ in $\mathbb{R}$), the value of this integral tends to $0$.
--
--   This is the local computation at a complex place in the analysis of the intertwining integral: the Möbius-twisting factor $|c'z+d'|^{2(2\sigma-1)}$ becomes trivial at the distinguished parameter $\sigma=1/2$, where the normalised complex absolute value contributes the exponent $2\sigma-1$. It is used in [`AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom`](thm.html#AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom), which compares the Möbius-shifted complex atom integral with the unshifted one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
    (c' d' : ℂ) (_h : c' ≠ 0 ∨ d' ≠ 0) (a b m : ℕ) (_habm : a + b ≤ m) :
    Tendsto (fun σ : ℝ =>
        ∫ z : ℂ, ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
          * (z ^ a * (starRingEnd ℂ) z ^ b
              * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by sorry
