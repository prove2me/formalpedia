-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
-- name    : AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/507ec09f-eab0-5785-b536-ae7d241481bc
-- title:
--   Vanishing of the Möbius weight correction as σdownarrow 1/2
-- statement:
--   Fix real numbers $c'$ and $d'$, a hypothesis that at least one of them is non-zero, and an integer $k$. Consider the complex-valued function of a real parameter $\sigma$ given by the Lebesgue integral over $x\in\mathbb{R}$ of the product of two factors: the real number $\bigl((c'x+d')^2\bigr)^{\sigma-1/2}-1$, formed with the real power function and then viewed in $\mathbb{C}$, and the quantity $\bigl((x-i)/\sqrt{1+x^2}\bigr)^{k}\,(1+x^2)^{-(\sigma+1/2)}$, where the $k$-th power is an integer power of a complex number and $(1+x^2)^{-(\sigma+1/2)}$ is the complex power of the positive real $1+x^2$ with complex exponent $-(\sigma+\tfrac12)$. The assertion is that this function of $\sigma$ tends to $0$ along the filter of right-hand neighbourhoods of $1/2$, i.e. $\sigma\to 1/2^{+}$. Note that the integral is the Bochner integral, so it is defined (as $0$) also for those $\sigma$ for which the integrand fails to be integrable.
--
--   This is the archimedean local estimate showing that, in the limit $\sigma\downarrow 1/2$, reweighting the real-place atom $\bigl((x-i)/\sqrt{1+x^2}\bigr)^{k}(1+x^2)^{-(\sigma+1/2)}$ by the Möbius Jacobian factor $\bigl((c'x+d')^2\bigr)^{\sigma-1/2}$ changes its integral by an amount going to $0$. It is used in [`AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom`](thm.html#AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom), where the difference between the integral of a Möbius-shifted atom and that of the unshifted atom is controlled at the edge parameter $\sigma=1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
    (c' d' : ℝ) (_h : c' ≠ 0 ∨ d' ≠ 0) (k : ℤ) :
    Tendsto (fun σ : ℝ =>
        ∫ x : ℝ, ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
          * (((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
              * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by sorry
