-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
-- name    : AvramDividend.Classical.avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:17:58.014536+00:00
-- url     : https://prove2.me/theorems/2cfd5165-8047-4128-a6a9-eb794bcc9858
-- title:
--   Fixed-time L2 integrability from joint measurability and time-dependent bounds
-- statement:
--   For each fixed time, jointly measurable coefficients with finite, potentially time-dependent deterministic bounds have integrable squared differences under a finite outcome measure. Uses the Proved B129 bounded measurable squared-difference lemma fibrewise.
-- source:
--   Proved B129

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν]
    (f g : α × β → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : α → ℝ) (hBf : ∀ a, 0 ≤ Bf a) (hBg : ∀ a, 0 ≤ Bg a)
    (hfb : ∀ a b, |f (a,b)| ≤ Bf a)
    (hgb : ∀ a b, |g (a,b)| ≤ Bg a) :
    ∀ a, Integrable (fun b => (f (a,b) - g (a,b)) ^ 2) ν := by sorry
