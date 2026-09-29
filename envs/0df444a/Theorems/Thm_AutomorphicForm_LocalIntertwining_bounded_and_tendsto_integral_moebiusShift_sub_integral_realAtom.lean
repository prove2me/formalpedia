-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
-- name    : AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/289d8a8d-07f6-58f6-a45d-defebb68079a
-- title:
--   Uniform bound and Möbius-shift limit for the real atom
-- statement:
--   Fix real numbers $a,b,c,d$ together with a hypothesis that $ad-bc\neq 0$, and an integer $k$. Introduce the family of complex-valued functions on $\mathbb{R}$, indexed by a real parameter $\sigma$, given by $$\mathrm{atom}_\sigma(x)=\Bigl(\frac{x-i}{\sqrt{1+x^2}}\Bigr)^{k}\,(1+x^2)^{-(\sigma+\frac12)},$$ where the $k$-th power is an integer power of a complex number and $(1+x^2)^{-(\sigma+1/2)}$ is the complex power of the positive real $1+x^2$ with exponent $-(\sigma+\frac12)$ regarded as a complex number. Two assertions are made. First, there is a constant $C\in\mathbb{R}$ such that for every real $\sigma$ with $1/2<\sigma\le 1$ one has $\bigl\|\int_{\mathbb{R}}\mathrm{atom}_\sigma(x)\,dx\bigr\|\le C$, the integrals being Bochner integrals against Lebesgue measure. Second, as $\sigma$ tends to $1/2$ from the right, $$\int_{\mathbb{R}}|ad-bc|^{\sigma+\frac12}\,|a+xc|^{-(2\sigma+1)}\,\mathrm{atom}_\sigma\!\Bigl(\frac{b+xd}{a+xc}\Bigr)dx-\int_{\mathbb{R}}\mathrm{atom}_\sigma(x)\,dx$$ tends to $0$, the limit being taken along the filter of right neighbourhoods of $1/2$ and again with the exponents of the positive real bases interpreted as complex powers.
--
--   This is the archimedean counterpart of the local "bounded, and difference tending to zero" estimate for the Weyl translate of a pure-tensor section: near the point $\sigma=1/2$ the real-place intertwining integral of the atom is insensitive, in the limit, to a Möbius substitution by a fixed element of $\mathrm{GL}_2(\mathbb{R})$. It feeds the statement [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt), and it is proved from the Möbius change-of-variables identity [`MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real`](thm.html#MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real) together with the limit [`AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half`](thm.html#AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by sorry
