-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_payment_times_supremum_clock_union
-- name    : AvramDividend.Classical.avram_wave4_04b_payment_times_supremum_clock_union
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:29:21.982131+00:00
-- url     : https://prove2.me/theorems/d3f7fe0f-2bae-455e-8bff-011d5a441a9f
-- title:
--   Chronological right-payment times commute with increasing-clock supremum, retaining the initial atom
-- statement:
--   For every sequence of extended nonnegative localisation clocks, the chronological dividend-payment set at the supremum clock is exactly the union of the payment sets at the individual clocks. The equality includes the initial payment at t=0 even when all clocks vanish, and carries no atom-only assumption. It is an exact source paymentTimes identity required to pass full Stieltjes rewards through increasing localisation.
-- source:
--   04-B controlled complete Stieltjes localisation, actual source paymentTimes definition

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_payment_times_supremum_clock_union
    (τ : ℕ → ℝ≥0∞) :
    paymentTimes (⨆ n, τ n) = ⋃ n, paymentTimes (τ n) := by
  sorry
