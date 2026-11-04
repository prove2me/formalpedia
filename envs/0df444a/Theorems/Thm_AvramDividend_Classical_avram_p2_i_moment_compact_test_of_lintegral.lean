-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_lintegral
-- name    : AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:56:12.699829+00:00
-- url     : https://prove2.me/theorems/ed0b6484-3c26-4e46-8254-0c861732a649
-- title:
--   Compact continuous tests converge directly from all finite ENNReal moments
-- statement:
--   General-filter source-ready corollary: finite positive measures with positive approximating support, unit-supported limit, integrable real monomials and all finite ENNReal monomial integral limits have convergent integrals of all continuous tests vanishing outside (0,1). This packages the accepted real moment-to-compact-test theorem and all-k extended-real moment conversion. The approximating measures may have positive mass above one.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hfinite : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by sorry
