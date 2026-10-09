-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_esscher_discounted_tail_kernel
-- name    : AvramDividend.Classical.positiveLaplace_esscher_discounted_tail_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:09:52.069977+00:00
-- url     : https://prove2.me/theorems/bc7b19b0-35a2-4c3f-addd-ff8331655e00
-- title:
--   Positive Laplace transform of the Esscher-discounted jump-tail renewal kernel
-- statement:
--   Weight any positive jump-magnitude measure μ by exp(-φz), form its positive half-line tail-density kernel κφ(dx)=μ_φ((x,∞))dx, and calculate its positive Laplace transform. It equals ∫ exp(-φz)(1-exp(-sz))/s dμ(z) for s>0. This is the exact root-shifted BV kernel, not the canonical non-root kernel with numerator 1-exp(-(s+φ)z). Prove by applying the existing Proved positive_laplace_tail_withDensity theorem to μ.withDensity(exp(-φz)), then the pinned Mathlib lintegral_withDensity_eq_lintegral_mul identity. This bridges the remaining root-shifted renewal construction to the already Proved generic convolution and geometric Laplace identities.
-- source:
--   Proved AvramDividend.Classical.positive_laplace_tail_withDensity; Mathlib MeasureTheory.lintegral_withDensity_eq_lintegral_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positiveLaplace_esscher_discounted_tail_kernel
    (μ : Measure ℝ≥0) (φ s : ℝ) (hs : 0 < s) :
    let μφ : Measure ℝ≥0 :=
      μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
    let κφ : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
    (∫⁻ x : ℝ,
      ENNReal.ofReal (Real.exp (-(s * x))) ∂κφ) =
    ∫⁻ z : ℝ≥0,
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s) ∂μ := by sorry
