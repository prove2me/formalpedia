-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_moments_imply_weak_convergence
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_unit_moments_imply_weak_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:28:15.47419+00:00
-- url     : https://prove2.me/theorems/a4da139f-8839-4b90-86d4-a459a9207a35
-- title:
--   Compactified original image monomial convergence determines weak convergence
-- statement:
--   For a filter-indexed family of genuine finite real image measures whose masses are eventually bounded and which are eventually supported on [0,1], convergence of all of their ENNReal.ofReal monomial moments to those of a fixed unit-supported finite measure implies weak convergence to that measure, using Prokhorov compactness, globally bounded continuous clamped-power tests, and finite Hausdorff moment uniqueness. The theorem works for arbitrary filters and does not require an independent candidate measure moment assumption.

import Mathlib
open MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_unit_moments_imply_weak_convergence
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hρunit : ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ,
      Tendsto (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i) l
        (nhds (∫⁻ z, (ENNReal.ofReal z) ^ k ∂ρ))) :
    Tendsto μi l (nhds ρ) := by sorry
