-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
-- name    : AutomorphicForm.ComplexIwasawa.exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ef9a3d76-4e96-5fcc-9e6d-aa1050f4c41e
-- title:
--   Uniform strip bound for the complex-place weight–Fourier integral
-- statement:
--   Fix natural numbers $a,b$ and reals $\sigma_1,\sigma_2$, and set
--   $$j(w,\zeta)=\int_{\mathbb C} z^{a}\,\overline{z}^{\,b}\,(1+\|z\|^{2})^{-w}\,\exp\!\big(-\,4\pi\,\mathrm{Re}(\zeta z)\,i\big)\,dz,$$
--   the Bochner integral over $\mathbb C$ with respect to the standard volume measure (so $j(w,\zeta)=0$ for those $(w,\zeta)$ where the integrand fails to be integrable). The assertion is the existence of an exponent $A_0\in\mathbb N$, depending only on $a,b,\sigma_1,\sigma_2$, such that for every $N\in\mathbb N$ there are a real $C$ and a natural number $A$ with $C>0$ and the following property: for every $\zeta\in\mathbb C$ with $\zeta\neq 0$, for every entire $J:\mathbb C\to\mathbb C$ (differentiable on all of $\mathbb C$) which agrees with $w\mapsto j(w,\zeta)$ on the half-plane $\mathrm{Re}\,w>\frac{a+b}{2}+1$, and for every $w$ with $\sigma_1\le \mathrm{Re}\,w\le\sigma_2$, one has
--   $$\|J(w)\|\le C\,(1+|\mathrm{Im}\,w|)^{A}\,\max(1,\|\zeta\|^{-1})^{A_0}\,(1+\|\zeta\|)^{-N}.$$
--   Thus $A_0$, the exponent governing the blow-up as $\zeta\to 0$, is quantified before $N$, while $C$ and the exponent $A$ of polynomial growth in $\mathrm{Im}\,w$ may depend on $N$ (as well as on $a,b,\sigma_1,\sigma_2$). The hypotheses on $J$ determine it uniquely on the strip by analytic continuation from the half-plane of convergence.
--
--   The integral $j(w,\zeta)$ is the archimedean weight–Fourier integral attached to a complex place in the Iwasawa decomposition for $\mathrm{GL}_2$, and the statement is the quantitative form of its meromorphic continuation to a vertical strip: rapid decay in the frequency $\zeta$, polynomial growth in $\mathrm{Im}\,w$, and a controlled pole order at $\zeta=0$ whose exponent is independent of the decay order. The ordering of quantifiers is what allows the small-frequency factors to be absorbed simultaneously across the places of a number field; it is used in the statement that Whittaker coefficients factor as an Euler product times an entire function with bounded growth in the archimedean parameters, and it relies on the continuity, holomorphy and polynomial-decay package [`AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`](thm.html#AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral) on the half-plane of absolute convergence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.ComplexIwasawa.exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
    (a b : ℕ) (σ₁ σ₂ : ℝ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ A₀ : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (A : ℕ), 0 < C ∧
      ∀ (ζ : ℂ), ζ ≠ 0 → ∀ (J : ℂ → ℂ), Differentiable ℂ J →
        (∀ w : ℂ, ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → J w = j w ζ) →
        ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
          ‖J w‖ ≤ C * (1 + |w.im|) ^ A * (max 1 ‖ζ‖⁻¹) ^ A₀ * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by sorry
