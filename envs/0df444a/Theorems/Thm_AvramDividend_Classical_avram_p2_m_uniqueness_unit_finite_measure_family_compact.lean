-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_family_compact
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:12:23.866455+00:00
-- url     : https://prove2.me/theorems/3f9b77e6-238b-4326-a0a5-5feeb8d88559
-- title:
--   Compactness of mass-bounded finite measures supported on the unit interval
-- statement:
--   For any nonnegative mass bound C, the family of finite real Borel measures with mass at most C and zero mass outside the closed unit interval is compact for the weak topology of finite measures. This is the exact pinned Prokhorov compactness interface needed when constructing a subsequential finite candidate for the original Lévy exponential-image moment limits.

import Mathlib.MeasureTheory.Measure.Prokhorov
open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure ℝ |
      μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0} := by sorry
