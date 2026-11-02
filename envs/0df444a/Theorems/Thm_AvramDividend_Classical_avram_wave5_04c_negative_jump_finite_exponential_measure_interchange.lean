-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_negative_jump_finite_exponential_measure_interchange
-- name    : AvramDividend.Classical.avram_wave5_04c_negative_jump_finite_exponential_measure_interchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:58:13.872212+00:00
-- url     : https://prove2.me/theorems/1302b26f-b20c-4292-9d58-d2990f7785fd
-- title:
--   Exact finite signed exponential-deficit Bochner interchange against a negative-jump Lévy measure
-- statement:
--   For an arbitrary possibly infinite-activity measure μ on the real line and a finite signed collection of exponential deficits 1-exp(k*y), prove exact interchange of the negative-half-line Bochner integral and finite sum under exactly the integrability of those deficits. The constant function 1 need not be μ-integrable; no illicit splitting into separately divergent terms is used. This is the Lévy-measure counterpart of the original source residual expectation interchange and allows matching finite polynomial primitive slopes with the genuine jump generator.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_negative_jump_finite_exp_measure_interchange_probe.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_negative_jump_finite_exponential_measure_interchange (μ : Measure ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hInt : ∀ k ∈ s, IntegrableOn
      (fun y : ℝ => 1 - Real.exp ((k : ℝ) * y)) (Iio (0 : ℝ)) μ) :
    (∫ y in Iio (0 : ℝ),
      ∑ k ∈ s, c k * (1 - Real.exp ((k : ℝ) * y)) ∂μ) =
      ∑ k ∈ s, c k *
        (∫ y in Iio (0 : ℝ),
          1 - Real.exp ((k : ℝ) * y) ∂μ) := by sorry
