-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_smooth_regular_C2_derivative_interchange_from_uniform_bounds
-- name    : AvramDividend.Classical.avram_ga_one_sided_smooth_regular_C2_derivative_interchange_from_uniform_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:57:24.647181+00:00
-- url     : https://prove2.me/theorems/7f26084a-1359-45d6-a955-b3a035c56e06
-- title:
--   Prove two derivatives commute with one-sided Gaussian HJB convolution from uniform smooth regular derivative bounds
-- statement:
--   Given a scalar C2 regular test f whose first and second derivatives exist with prescribed HasDerivAt witnesses and uniform global bounds, a measurable integrable one-sided kernel weight φ, and integrable weighted translates of f, f' and f'', prove rather than assume both derivative-under-integral identities for K(y)=∫φ(z)f(y-εz)dμ. Apply Mathlib's dominated local parameter-integral differentiability theorem twice. This discharges the real differentiation-interchange hypotheses for smooth regular components of the original zero-ν Lévy generator convolution, separating them correctly from the exceptional negative cap-kink Dirac term.
-- source:
--   Original Gaussian finitecap source 0ef5d778 and Proved ec2fc3be require explicit first/second derivative exchanges. This lemma establishes them under strong but transparent uniform smooth regularity bounds for the non-kink component. The nonsmooth cap kink is isolated for the separate distributional calculation.

import Mathlib
open MeasureTheory Filter Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_one_sided_smooth_regular_C2_derivative_interchange_from_uniform_bounds
    (μ : Measure ℝ) (φ f : ℝ → ℝ) (ε : ℝ)
    (hFI : ∀ y : ℝ, Integrable (fun z => φ z * f (y - ε * z)) μ)
    (hD1I : ∀ y : ℝ, Integrable
      (fun z => φ z * deriv f (y - ε * z)) μ)
    (hD2I : ∀ y : ℝ, Integrable
      (fun z => φ z * iteratedDeriv 2 f (y - ε * z)) μ)
    (hφI : Integrable (fun z => |φ z|) μ)
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hBd₁ : ∀ y, |deriv f y| ≤ L₁)
    (hBd₂ : ∀ y, |iteratedDeriv 2 f y| ≤ L₂)
    (hd₁ : ∀ y, HasDerivAt f (deriv f y) y)
    (hd₂ : ∀ y, HasDerivAt (deriv f) (iteratedDeriv 2 f y) y)
    (y : ℝ) :
    deriv (fun t => ∫ z, φ z * f (t - ε * z) ∂μ) y =
      ∫ z, φ z * deriv f (y - ε * z) ∂μ ∧
    iteratedDeriv 2 (fun t => ∫ z, φ z * f (t - ε * z) ∂μ) y =
      ∫ z, φ z * iteratedDeriv 2 f (y - ε * z) ∂μ := by sorry
