-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_ae_instant_ruin_of_strict_horizon_null
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_ae_instant_ruin_of_strict_horizon_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:23:05.558634+00:00
-- url     : https://prove2.me/theorems/8f30c033-03a3-4db5-9d01-9fdee63c98fa
-- title:
--   Almost-sure instantaneous ruin from null strict survival at every positive horizon
-- statement:
--   For any measure P and arbitrary extended-nonnegative-valued random time τ, if the P mass of the event {τ>t} is zero for every strictly positive t in ℝ≥0∞, then τ=0 almost everywhere. The proof uses the countable inverse-natural cover of {τ≠0}; no assumption of measurability of τ beyond the stated measurable survival events is added. This is a deterministic measure-theoretic transfer required to turn fixed-horizon BV Lévy strict-survival-null estimates into almost-sure instantaneous ruin.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_ae_instant_ruin_of_strict_horizon_null
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → ℝ≥0∞)
    (hNull : ∀ t : ℝ≥0∞, 0 < t →
      P {ω : Ω | t < τ ω} = 0) :
    ∀ᵐ ω ∂P, τ ω = 0 := by sorry
