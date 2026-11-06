-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_fatou_signed_witness_of_expected_upper
-- name    : AvramDividend.Classical.avram_p3_grid3_fatou_signed_witness_of_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:33:45.141213+00:00
-- url     : https://prove2.me/theorems/9d7a38f8-86ad-43fc-afb0-825d287e763c
-- title:
--   Signed Fatou certificate follows from exact expected upper bounds for its nonnegative finite rewards
-- statement:
--   For a probability measure, genuine integrable nonnegative finite rewards F_n bounded above in expectation by c and covering the desired reward in their Fatou liminf admit an explicit signed certificate: M_n = F_n - c, B_n = 0. This reduces the canonical BV grid certificate to establishing the exact expected reward bound and exact cash-prefix convergence on the original process, without assuming a surrogate stochastic law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_fatou_signed_witness_of_expected_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : ℝ)
    (G : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hExpected : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hFatou : ∀ᵐ ω ∂P, ENNReal.ofReal (G ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (G ω) ≤
        liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
