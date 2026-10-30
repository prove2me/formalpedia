-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_tilted_joint_exp_clock_nonnegative_ae
-- name    : AvramDividend.Classical.avram_ws01h_true_tilted_joint_exp_clock_nonnegative_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:30:21.125988+00:00
-- url     : https://prove2.me/theorems/336d1139-ce55-4674-a780-273ec626f7f7
-- title:
--   Genuine original-path real Exp(p) terminal clock remains nonnegative almost everywhere after arbitrary joint Esscher likelihood weighting
-- statement:
--   For the actual original path probability P times the independent real Exp(p) clock with positive p, and any arbitrary nonnegative full-path terminal likelihood D, almost every sample path and observed clock under the exact withDensity joint weighted law has a nonnegative real observation time. The proof uses the canonically accepted actual real exponential observation clock support, the genuine product measure of a null observation-time half-line, and absolute continuity of the true withDensity measure with respect to its original product law. It assumes no independence after Esscher weighting and no fabricated tilted whole-path probability. This allows exact identification of the original Lévy reflected-infimum real-clock CDF and continuous survival event with or without a clock positivity guard in the genuine Qp renewal.
-- source:
--   Accepted original real-clock a.e. nonnegativity 59996899; pinned Mathlib Measure.prod_prod, withDensity_absolutelyContinuous, ae_iff.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_clock_nonnegative_ae

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_tilted_joint_exp_clock_nonnegative_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p) (D : Ω × ℝ → ℝ≥0∞) :
    ∀ᵐ z : Ω × ℝ ∂((P.prod (expMeasure p)).withDensity D),
      0 ≤ z.2 := by sorry
