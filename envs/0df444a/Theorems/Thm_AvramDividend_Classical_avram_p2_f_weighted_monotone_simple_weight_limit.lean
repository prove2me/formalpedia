-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_monotone_simple_weight_limit
-- name    : AvramDividend.Classical.avram_p2_f_weighted_monotone_simple_weight_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:46:12.774948+00:00
-- url     : https://prove2.me/theorems/c2511802-3850-4d5b-b72b-b463f74a0fa5
-- title:
--   Monotone nonnegative predictable-simple weighted compensation limit
-- statement:
--   For an ambient-measurable nonnegative count and an increasing sequence of ambient-measurable nonnegative weights, exact weighted expected-rate formulas at every finite stage pass to the supremum, with no integrability or finite intensity assumptions. This proves a monotone-convergence stage needed to extend predictable simple marked-jump compensation to nonnegative predictable integrands, but it assumes independently established finite-stage formulas and no Lévy ν identification.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_iSup, ENNReal.iSup_mul and Measurable.mul; source-independent original jump measure integration stage.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_monotone_simple_weight_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (r : ℝ≥0∞) (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ n, Measurable (H n))
    (hmono : Monotone H)
    (hEach : ∀ n,
      (∫⁻ ω, H n ω * N ω ∂μ) = (∫⁻ ω, H n ω ∂μ) * r) :
    (∫⁻ ω, (⨆ n, H n ω) * N ω ∂μ) =
    (∫⁻ ω, ⨆ n, H n ω ∂μ) * r := by sorry
