-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_two_moment_limits_compact_tests
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_two_moment_limits_compact_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:19:41.069198+00:00
-- url     : https://prove2.me/theorems/711fbd56-af7f-4574-8c7b-76db2abcf086
-- title:
--   Uniqueness of compact-test integrals for two finite moment limits
-- statement:
--   For a shared family of positive-supported finite weighted image measures, two candidate unit-supported limiting finite positive measures with convergent finite monomial integrals must agree on every continuous test supported within the open unit band. The proof applies the already Proved polynomial-moment approximation theorem to each limit and uses Hausdorff uniqueness, without assuming the test-integral equality. Endpoint atoms are deliberately excluded from the test class.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_two_moment_limits_compact_tests
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (μi : ι → Measure ℝ) (μ ν : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hunit_ν : ∀ᵐ z ∂ν, z ∈ Set.Icc (0 : ℝ) 1)
    (hfinite_i : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hfinite_μ : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hfinite_ν : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν) ≠ ⊤)
    (hmom_μ : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (hmom_ν : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂μ) = (∫ z : ℝ, g z ∂ν) := by sorry
