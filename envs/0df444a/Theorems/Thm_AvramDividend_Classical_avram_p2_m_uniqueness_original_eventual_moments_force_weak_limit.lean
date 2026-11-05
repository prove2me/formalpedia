-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_eventual_moments_force_weak_limit
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_eventual_moments_force_weak_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:41:28.035267+00:00
-- url     : https://prove2.me/theorems/d96537c8-90a2-4017-b175-34a441ae1418
-- title:
--   Original compact-unit moment limits force an eventual finite weak limit
-- statement:
--   For genuine original measure laws which have eventually bounded finite total mass, eventual [0,1] support, and monomial moments converging to a fixed finite candidate measure on [0,1], construct an eventually equal finite-measure family converging weakly to that candidate. This joins the finite-carrier and Hausdorff-moment weak-convergence bridges without replacing the original-law moment premise by an assumed measure limit.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_eventual_moments_force_weak_limit
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hmass : ∀ᶠ i in l, (μi i) Set.univ ≤ C)
    (hunit : ∀ᶠ i in l, ∀ᵐ z ∂μi i, z ∈ Set.Icc (0 : ℝ) 1)
    (ρ : FiniteMeasure ℝ)
    (hρunit : ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ,
      Tendsto (fun i => ∫⁻ z, (ENNReal.ofReal z) ^ k ∂μi i) l
        (nhds (∫⁻ z, (ENNReal.ofReal z) ^ k ∂ρ))) :
    ∃ νi : ι → FiniteMeasure ℝ,
      (∀ᶠ i in l, (νi i : Measure ℝ) = μi i) ∧
      Tendsto νi l (nhds ρ) := by sorry
