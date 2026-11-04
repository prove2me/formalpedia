-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_tendsto
-- name    : AvramDividend.Classical.avram_p2_i_moment_compact_test_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:36:13.117809+00:00
-- url     : https://prove2.me/theorems/16051ad6-07f2-4709-afd0-4b32f2b02f9b
-- title:
--   All finite positive-measure moments imply compact continuous-test convergence
-- statement:
--   Under a general filter, let finite positive Borel measures μ_i be supported on the strictly positive real line and let their finite limit measure μ be supported on [0,1]. Suppose all real polynomial moments exist and every monomial integral converges to the limiting moment. Then integrals converge for every continuous real test vanishing on (-infinity,0] and [1,infinity), including all compact tests supported inside (0,1). The approximating measures are explicitly allowed to have mass above 1. The substantive proof uses Weierstrass on [0,2], finite polynomial moment convergence and arbitrarily high moments to suppress the z>2 polynomial tail. No conclusion is assumed.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_compact_test_tendsto
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by sorry
