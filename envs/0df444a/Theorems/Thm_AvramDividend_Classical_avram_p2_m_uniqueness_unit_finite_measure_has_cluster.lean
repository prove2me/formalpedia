-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_has_cluster
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_has_cluster
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:12:25.941958+00:00
-- url     : https://prove2.me/theorems/44d4a727-89ca-4ced-aa4e-0755916fce5f
-- title:
--   Weak cluster point of uniformly mass-bounded unit-supported finite measures
-- statement:
--   For every nontrivial filter, a family of finite real Borel measures with a common mass bound and support on the closed unit interval has a weak cluster-point measure satisfying the same mass and support bounds. The proof uses compactness without assuming sequential or first-countable weak convergence on finite measures; it is the precise candidate-existence bridge for original Lévy exponential-image limits.

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactness.Compact
open MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_has_cluster
    {ι : Type*} (l : Filter ι) [NeBot l]
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ)
    (hmass : ∀ i, (μi i).mass ≤ C)
    (hunit : ∀ i, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∃ μ : FiniteMeasure ℝ,
      μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        MapClusterPt μ l μi := by sorry
