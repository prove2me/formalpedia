-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_unit_ennreal_moment_measures_eq
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_finite_unit_ennreal_moment_measures_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:01:08.905265+00:00
-- url     : https://prove2.me/theorems/674ed39c-01bf-4f88-94ef-b4dc6e9d4a3b
-- title:
--   All ENNReal Hausdorff moments determine a finite regular unit-supported measure
-- statement:
--   Two finite regular positive measures supported almost everywhere on [0,1] with equal ENNReal moments of every natural order are equal on every Borel set, including both endpoints. Unlike the earlier P2-M measure-uniqueness target, all real-monomial integrability and ENNReal finiteness hypotheses are discharged automatically using Proved P2-I high-moment domination and finite-lintegral integrability. This is a reusable source-independent uniqueness bridge for P2-B's finite original-law image candidate, and does not assume the desired equality, tightness on an unbounded domain, or marked-count intensity.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_finite_unit_ennreal_moment_measures_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hunit_ν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) :
    μ = ν := by sorry
