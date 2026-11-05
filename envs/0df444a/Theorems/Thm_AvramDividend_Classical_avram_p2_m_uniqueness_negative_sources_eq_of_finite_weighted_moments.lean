-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_sources_eq_of_finite_weighted_moments
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_negative_sources_eq_of_finite_weighted_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:48:50.07519+00:00
-- url     : https://prove2.me/theorems/a9f40d6f-bd1b-4185-ba11-ae641045f4c7
-- title:
--   Negative Borel measures determined by finite weighted moments without regularity hypotheses
-- statement:
--   Arbitrary possibly infinite Borel measures concentrated almost everywhere on strictly negative real marks are equal whenever their fourth-weighted exponential pushforwards are finite and have matching ENNReal polynomial moments. The finite image is compactly supported by source negativity, and regularity is an automatically dischargeable property of finite Borel measures on the real line. This provides a leaner original source-versus-intrinsic mark-rate uniqueness interface for P2-B, leaving the genuine candidate moment identity as an independent obligation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_negative_sources_eq_of_finite_weighted_moments
    (μ ν η ρ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ]
    (hnegμ : ∀ᵐ y ∂μ, y < 0)
    (hnegν : ∀ᵐ y ∂ν, y < 0)
    (hη : η = ((μ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hρ : ρ = ((ν.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ)) :
    μ = ν := by sorry
