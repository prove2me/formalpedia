-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:47:56.796438+00:00
-- url     : https://prove2.me/theorems/1c39ee30-2eca-4f5c-bcda-862a85acc000
-- title:
--   Finite real unit-supported measures are determined by ENNReal moments without explicit regularity
-- statement:
--   Two finite positive Borel measures on the real line, each almost everywhere concentrated on [0,1], are equal if every ENNReal nonnegative-integer moment coincides. Their usual real-line Radon regularity is supplied by the finite-measure topology rather than assumed in the theorem signature. The proof imports the independently Proved P2-M Hausdorff moment extension. No unbounded moment problem, tightness on an unbounded domain, or original Lévy rate is assumed.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hunitμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hunitν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) :
    μ = ν := by sorry
