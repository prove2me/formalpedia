-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_discount_cash_integrable_finite_measure
-- name    : AvramDividend.Classical.avram_ga_discount_cash_integrable_finite_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:31:34.04123+00:00
-- url     : https://prove2.me/theorems/b8e914fe-9974-4c40-8a04-1d1d03b13207
-- title:
--   Integrability of discounted cash after cap occupation and Gaussian limit on finite measures
-- statement:
--   Under a finite measure, integrability of stopped discounted cash, cap occupation and Gaussian L1 limit implies integrability of their adjusted signed difference. The finite-measure premise is essential for nonzero deterministic cash constants.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_discount_cash_integrable_finite_measure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (F Occ Z : Ω → ℝ) (a b c : ℝ)
    (hFI : Integrable F μ) (hOcc : Integrable Occ μ)
    (hZI : Integrable Z μ) :
    Integrable (fun ω => F ω - a - (b + c * Occ ω) - Z ω) μ := by sorry
