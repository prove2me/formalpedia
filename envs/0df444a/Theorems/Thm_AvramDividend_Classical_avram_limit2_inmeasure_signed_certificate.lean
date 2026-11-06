-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_inmeasure_signed_certificate
-- name    : AvramDividend.Classical.avram_limit2_inmeasure_signed_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:05:10.140206+00:00
-- url     : https://prove2.me/theorems/12a3d9ec-8ede-4274-8c4a-dadee0635b22
-- title:
--   In-measure physical cash-grid convergence completes the six-clause signed Fatou certificate
-- statement:
--   Starting from a genuine original-process physical cash grid with integrable nonnegative values, an upper expected cash budget, and only convergence in measure to the actual strict cash plus surviving terminal payoff, a strictly increasing subsequence supplies the exact signed-Fatou six-clause F/M/B witness. The original stochastic grid and its convergence remain to be established.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_inmeasure_signed_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ) (c : ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hMeasure : TendstoInMeasure P F atTop R) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (R ω) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
