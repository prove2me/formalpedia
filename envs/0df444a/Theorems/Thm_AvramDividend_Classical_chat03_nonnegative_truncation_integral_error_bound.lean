-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_error_bound
-- name    : AvramDividend.Classical.chat03_nonnegative_truncation_integral_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:19:33.076107+00:00
-- url     : https://prove2.me/theorems/951b3505-163d-4f10-89f2-d750c73c62bd
-- title:
--   Uniform real truncation error from the second moment
-- statement:
--   On a probability space, let Y be almost-everywhere nonnegative and measurable, with integrable square and bounded second moment C. For any positive cutoff R, the difference between the real expectation of Y and that of min(Y,R) is nonnegative and at most C divided by R. All integrals are justified by established L2-to-L1 and bounded-clipping integrability lemmas.
-- source:
--   Pointwise truncation-gap quadratic domination, Bochner integral monotonicity and linearity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_min_truncation_gap_le_quadratic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncated_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_integrable_real_square

open MeasureTheory AvramDividend.Classical

theorem AvramDividend.Classical.chat03_nonnegative_truncation_integral_error_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (R C : ℝ) (hR : 0 < R)
    (hYm : AEStronglyMeasurable Y P)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P ∧
      ∫ ω, (Y ω) ^ 2 ∂P ≤ C) :
    0 ≤ (∫ ω, Y ω ∂P) - (∫ ω, min (Y ω) R ∂P) ∧
      (∫ ω, Y ω ∂P) - (∫ ω, min (Y ω) R ∂P) ≤ C / R := by sorry
