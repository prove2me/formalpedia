-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:23:21.056509+00:00
-- url     : https://prove2.me/theorems/55138b2c-c107-48c5-9dd4-4cef9bd82b78
-- title:
--   Weak convergence from eventual unit support and unique cluster points
-- statement:
--   For a filter-indexed family of finite real Borel measures, eventual mass bounded by C and eventual support on [0,1], together with equality of every weak cluster point in the compact family to the same candidate rho, imply full weak convergence to rho. This directly addresses the eventual small-time bounds available for original Lévy exponential-image laws.

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactness.Compact
open MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hunique : ∀ σ : FiniteMeasure ℝ,
      σ.mass ≤ C → σ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        MapClusterPt σ l μi → σ = ρ) :
    Tendsto μi l (nhds ρ) := by sorry
