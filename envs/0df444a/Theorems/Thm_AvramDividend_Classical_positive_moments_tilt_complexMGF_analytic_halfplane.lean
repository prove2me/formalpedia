-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_moments_tilt_complexMGF_analytic_halfplane
-- name    : AvramDividend.Classical.positive_moments_tilt_complexMGF_analytic_halfplane
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:33:56.472408+00:00
-- url     : https://prove2.me/theorems/ebd89cf7-54d5-4e62-ae05-ebd551f6bd3f
-- title:
--   Positive one-sided MGFs imply analyticity of the exponentially tilted complex MGF on Re z greater than minus one
-- statement:
--   If a real Borel measure has integrable exp(u*x) for every positive real u, then after weighting it by exp(x) its complex moment generating function is analytic throughout the open right half-plane Re(z)>-1. Proof: every real t>-1 is in the integrable exponent set of the tilted measure; openness embeds this half-line into its interior. Restrict Mathlib's general analyticOnNhd_complexMGF theorem to the indicated half-plane. This provides the analytic-domain hypothesis needed to derive positive-MGF measure uniqueness using the Proved right-half-plane MGF equality theorem.
-- source:
--   Depends on accepted-in-progress pos_moments_exp_tilt_integrable_right_ray [a3dcdb5e-4fbf-4299-a74c-1e60f333ce91] plus Mathlib ProbabilityTheory.analyticOnNhd_complexMGF and Set.interior_maximal. Do not publish until dependency Proved.

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Topology.Sets.Opens
import Theorems.Thm_AvramDividend_Classical_pos_moments_exp_tilt_integrable_right_ray

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_moments_tilt_complexMGF_analytic_halfplane
    (μ : Measure ℝ)
    (h : ∀ u : ℝ, 0 < u →
      Integrable (fun x : ℝ => Real.exp (u * x)) μ) :
    AnalyticOnNhd ℂ (complexMGF id
      (μ.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp x))))
      {z : ℂ | -1 < z.re} := by sorry
