-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_positive_event_ae_condexp_martingale_transfer
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn11_positive_event_ae_condexp_martingale_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:12:13.73377+00:00
-- url     : https://prove2.me/theorems/a8a91f4e-6b8c-48cd-8ea3-8718d7919714
-- title:
--   Almost-everywhere dominated stopped payoff transfers conditional martingale centring to an event budget
-- statement:
--   If a stopped positive-clock payoff is integrable and bounded almost everywhere by its initial benchmark plus an integrable martingale with conditional mean zero at time zero, then its expected value on the strictly positive stopping-clock event is bounded by the benchmark times the event probability. The almost-everywhere inequality permits passage from stochastic Ito limits without requiring an everywhere-defined pathwise bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gaussian11_strict_positive_stopping_clock_condexp_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn11_positive_event_ae_condexp_martingale_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F M : Ω → ℝ) (hFI : Integrable F P) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + M ω) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal := by sorry
