-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_eventually_unit_finite_measure_has_cluster
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_has_cluster
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:23:24.890118+00:00
-- url     : https://prove2.me/theorems/31cf057c-54f7-43fe-8c2e-86d6cf7982b6
-- title:
--   Weak cluster point from eventual mass bound and unit support
-- statement:
--   For a family of finite Borel measures indexed by a nontrivial filter, an eventual uniform mass bound and eventual support in the closed unit interval imply the existence of a weak cluster-point measure with the same properties. This directly matches the small-time original-process bounds without having to modify exceptional parameter values.

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactness.Compact
open MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_has_cluster
    {ι : Type*} (l : Filter ι) [NeBot l]
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∃ μ : FiniteMeasure ℝ,
      μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        MapClusterPt μ l μi := by sorry
