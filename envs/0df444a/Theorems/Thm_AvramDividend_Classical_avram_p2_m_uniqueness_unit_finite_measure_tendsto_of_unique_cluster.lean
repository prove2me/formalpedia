-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_tendsto_of_unique_cluster
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_tendsto_of_unique_cluster
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:12:34.380774+00:00
-- url     : https://prove2.me/theorems/75c361b6-820c-4fa2-aae8-66c74535a47f
-- title:
--   Convergence of unit-supported finite measures from unique weak cluster points
-- statement:
--   If all finite Borel measures in a filter-indexed family are supported on the closed unit interval and have mass bounded by C, and every weak cluster-point measure satisfying the bounds equals a fixed candidate rho, then the entire family converges weakly to rho. The result uses compactness directly and requires no sequential compactness or first-countability of the space of finite measures. It is designed for the small-time original Lévy moment-limit construction.

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactness.Compact
open MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_tendsto_of_unique_cluster
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ i, (μi i).mass ≤ C)
    (hunit : ∀ i, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hunique : ∀ σ : FiniteMeasure ℝ,
      σ.mass ≤ C → σ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        MapClusterPt σ l μi → σ = ρ) :
    Tendsto μi l (nhds ρ) := by sorry
