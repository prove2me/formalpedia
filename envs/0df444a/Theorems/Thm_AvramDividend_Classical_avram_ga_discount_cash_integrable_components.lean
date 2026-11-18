-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_discount_cash_integrable_components
-- name    : AvramDividend.Classical.avram_ga_discount_cash_integrable_components
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-17T17:24:28.868181+00:00
-- url     : https://prove2.me/theorems/e30069b9-7864-462e-b4dd-2da87d2adc9a
-- title:
--   Integrable finitecap cash minus occupation and mesh limit
-- statement:
--   Integrability closure of source stopped cash, deterministic cost, occupation and Gaussian L1 limit.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_discount_cash_integrable_components
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F Occ Z : Ω → ℝ) (a b c : ℝ)
    (hFI : Integrable F μ) (hOcc : Integrable Occ μ)
    (hZI : Integrable Z μ) :
    Integrable (fun ω => F ω - a - (b + c * Occ ω) - Z ω) μ := by sorry
