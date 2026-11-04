-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_lintegral_moments
-- name    : AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:31:31.29709+00:00
-- url     : https://prove2.me/theorems/b4c643b2-4e2e-48f0-92b8-5a71e6fd7182
-- title:
--   All finite ENNReal moments imply compact-test convergence without separate mass or integrability hypotheses
-- statement:
--   For a general filter, positive-supported measures μ_i and a limit measure supported on [0,1], assume every ENNReal monomial moment is finite at each i and at the limit and those ENNReal moments converge. Then integrals of every continuous test vanishing outside (0,1) converge. The k=0 finite moment gives finite total mass and each finite kth moment gives real-integrability, so no redundant mass/integrability premises remain. Approximants may have mass above 1.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral_moments
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hmom_i_finite : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hmom_μ_finite : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by sorry
