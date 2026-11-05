-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_all_lintegral_tendsto_real
-- name    : AvramDividend.Classical.avram_p2_i_moment_all_lintegral_tendsto_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:54:04.725549+00:00
-- url     : https://prove2.me/theorems/ea3089fd-5374-4a69-9a5f-37246c973583
-- title:
--   All extended-real monomial integral limits imply all real moment limits
-- statement:
--   For nonnegative-supported finite real measures under a general filter, convert the entire family of finite extended-real monomial-integral convergence hypotheses into convergence of all real monomial integrals, using the independently proven single-moment conversion. This is the exact collection-valued interface needed by the compact-test moment theorem, without assuming compact support for approximants.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_all_lintegral_tendsto_real
    {ι : Type*} (l : Filter ι) (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 ≤ z)
    (hpositive_μ : ∀ᵐ z ∂μ, 0 ≤ z)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hfinite : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ))) :
    ∀ k, Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
      (nhds (∫ z : ℝ, z ^ k ∂μ)) := by sorry
