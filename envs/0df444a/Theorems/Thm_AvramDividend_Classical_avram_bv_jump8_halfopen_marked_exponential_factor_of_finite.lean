-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_halfopen_marked_exponential_factor_of_finite
-- name    : AvramDividend.Classical.avram_bv_jump8_halfopen_marked_exponential_factor_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:21:01.099203+00:00
-- url     : https://prove2.me/theorems/fa7db8c8-48af-4c48-bc33-01ede4bdc618
-- title:
--   Finite intrinsic marked Laplace weights multiply across adjacent positive-time windows
-- statement:
--   For a measurable nonnegative mark weight and any time-mark measure, finite integrals on adjacent half-open windows (0,s] and (s,t] imply exact multiplication of the corresponding real Laplace weights on (0,t]. This combines the already proved half-open nonnegative integral split with the finite-toReal addition rule and exponential addition. Finite-cutoff source marks must separately be shown finite; no stochastic independence is assumed.
-- source:
--   Use Proved exact nonnegative half-open marked lintegral split 59ce92e1. ENNReal.toReal_add hLeft hRight is valid because both contributions are not top. Real.exp_add after unary minus gives the product. Application to the original Lévy marked process requires source-specific finiteness of the cutoff-weighted integrals.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_halfopen_marked_lintegral_split
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_halfopen_marked_exponential_factor_of_finite
    (μ : Measure (ℝ≥0 × ℝ))
    (g : ℝ≥0 × ℝ → ℝ≥0∞) (hg : Measurable g)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hLeft : (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ s then g p else 0 ∂μ) ≠ ∞)
    (hRight : (∫⁻ p : ℝ≥0 × ℝ, if s < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ) ≠ ∞) :
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ).toReal)) =
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ s then g p else 0 ∂μ).toReal)) *
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ, if s < p.1 ∧ p.1 ≤ t then g p else 0 ∂μ).toReal)) := by sorry
