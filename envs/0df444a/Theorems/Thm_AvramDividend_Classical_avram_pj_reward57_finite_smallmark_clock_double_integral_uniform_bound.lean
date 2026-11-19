-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward57_finite_smallmark_clock_double_integral_uniform_bound
-- name    : AvramDividend.Classical.avram_pj_reward57_finite_smallmark_clock_double_integral_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:46:40.918089+00:00
-- url     : https://prove2.me/theorems/c21f3459-eb98-4bfc-8dfa-526a1a73bed9
-- title:
--   Finite signed small-mark stopped clock bound with explicit bounded-mark requirement
-- statement:
--   For any two finite measures, a finite mark band B whose marks satisfy |z|<=1, a bounded time-dependent real coefficient g, a bounded stop and nonnegative discount q, the stopped double signed integral is bounded by M*ν(B)*μ(univ). The mark bound is essential: without it the claim fails for large marks. Will be used with original (-1,-eta) physical mark band.
-- source:
--   Proved avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le; physical B=Ioo(-1,-eta) satisfies |z|<=1.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward57_finite_smallmark_clock_double_integral_uniform_bound
    (μ : Measure ℝ≥0) (hμ : μ Set.univ < ⊤)
    (ν : Measure ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (hν : ν B < ⊤)
    (hBsmall : ∀ z ∈ B, |z| ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (τ : ℝ≥0)
    (g : ℝ≥0 → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ t, |g t| ≤ M) :
    |∫ t, ∫ z,
      (if t ≤ τ ∧ z ∈ B then
        Real.exp (-(q * (t : ℝ))) * (g t * z) else 0) ∂ν ∂μ| ≤
      (M * (ν B).toReal) * (μ Set.univ).toReal := by sorry
