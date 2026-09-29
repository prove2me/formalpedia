-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
-- name    : AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/474b9ae6-48a5-58ee-a395-a246951bd673
-- title:
--   Complex-place atom: uniform bound and Möbius-shift limit
-- statement:
--   Fix $a,b,c,d\in\mathbb{C}$ with $ad-bc\neq 0$ and natural numbers $a_0,b_0,m$ with $a_0+b_0\le m$, and let the family of functions $\mathrm{atom}:\mathbb{R}\to\mathbb{C}\to\mathbb{C}$ be given by $$\mathrm{atom}_\sigma(z)=z^{a_0}\,\overline{z}^{\,b_0}\,(1+\|z\|^{2})^{-(2\sigma+1)-m/2},$$ where the positive real $1+\|z\|^2$ is cast into $\mathbb{C}$ and raised to the indicated complex exponent. Two assertions are made simultaneously. First, there is a constant $C\in\mathbb{R}$ such that for every real $\sigma$ with $1/2<\sigma\le 1$ one has $\|\int_{\mathbb{C}}\mathrm{atom}_\sigma(z)\,dz\|\le C$, the integral being taken against the standard volume measure on $\mathbb{C}$. Secondly, along the filter of points approaching $1/2$ from above, the function $$\sigma\mapsto \int_{\mathbb{C}}\big(\|ad-bc\|^{2}\big)^{\sigma+1/2}\big(\|a+zc\|^{2}\big)^{-(2\sigma+1)}\,\mathrm{atom}_\sigma\!\left(\frac{b+zd}{a+zc}\right)dz\;-\;\int_{\mathbb{C}}\mathrm{atom}_\sigma(z)\,dz$$ tends to $0$; here again the real quantities $\|ad-bc\|^2$ and $\|a+zc\|^2$ are cast into $\mathbb{C}$ and the exponents are complex.
--
--   This is the complex-place archimedean input to the analysis of intertwining integrals: the Möbius substitution $z\mapsto (b+zd)/(a+zc)$ attached to an element of $\mathrm{GL}_2(\mathbb{C})$ moves the integral of the weight-$(a_0,b_0)$ atom only by an amount vanishing as the spectral parameter approaches the edge $\sigma=1/2$, while the integrals themselves stay bounded there. It is used, together with the complex Möbius change-of-variables formula [`MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex`](thm.html#MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex) and the companion limit [`AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half`](thm.html#AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half), in proving that the normalised Weyl intertwining integral of a flat family has vanishing limit at $\sigma=1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ z, atom σ z‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ z : ℂ, (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + z * d) / (a + z * c)))
          - ∫ z : ℂ, atom σ z)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by sorry
