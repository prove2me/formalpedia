-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_unit_moments_inherit_cluster_limit
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_unit_moments_inherit_cluster_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:26:07.097589+00:00
-- url     : https://prove2.me/theorems/24b6f3c7-2049-4893-afa8-9a8cf1ac8724
-- title:
--   Original unit-supported monomial limits pass to weak cluster points
-- statement:
--   If the original finite image measures are eventually carried by [0,1], any of their weak cluster points supported on [0,1] inherits the limit of each original ENNReal.ofReal monomial moment, provided that monomial has a globally bounded continuous NNReal-valued extension on [0,1]. This directly composes the true original-process moment-limit premises with the pinned weak-cluster topology.

import Mathlib
open MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_unit_moments_inherit_cluster_limit
    {ι : Type*} (l : Filter ι)
    (μi : ι → FiniteMeasure ℝ) (σ : FiniteMeasure ℝ)
    (hcluster : MapClusterPt σ l μi)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hσunit : σ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (g : ℝ →ᵇ ℝ≥0) (k : ℕ)
    (hagree : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
      (g z : ℝ≥0∞) = (ENNReal.ofReal z) ^ k)
    (a : ℝ≥0∞)
    (hlim : Tendsto (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i)
      l (nhds a)) :
    (∫⁻ z, (ENNReal.ofReal z) ^ k ∂σ) = a := by sorry
