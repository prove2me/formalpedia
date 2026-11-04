-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_finite_lintegrals
-- name    : AvramDividend.Classical.avram_p2_i_moment_compact_test_of_finite_lintegrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:31:21.741742+00:00
-- url     : https://prove2.me/theorems/c02ab0e5-c347-4136-a741-151b7206817b
-- title:
--   Compact tests from finite ENNReal moments without Bochner integrability assumptions
-- statement:
--   The general-filter finite-measure moment-to-compact-test theorem for positive-supported approximating measures and [0,1]-supported limit, assuming only finite ENNReal monomial moments for each approximant and limit plus convergence of their ENNReal moments. Real Bochner integrability follows automatically from the positivity and finite ENNReal moments, so P2-B need not independently establish it for every polynomial power. Approximating measures may put mass above 1.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_compact_test_of_finite_lintegrals
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
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
