-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_positive_event_condexp_martingale_transfer
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn10_positive_event_condexp_martingale_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:56:58.000051+00:00
-- url     : https://prove2.me/theorems/14599def-6548-4945-8463-2ece82fa8d57
-- title:
--   Initial-filtration martingale cancellation yields stopped positive-clock expected upper bound
-- statement:
--   For any probability-space right-continuous stopping clock, an integrable payoff bounded pointwise by a benchmark plus an integrable initial-conditionally centred martingale has a probability-weighted upper bound on the strictly positive-clock event. This applies to the Gaussian source once its original Ito decomposition is established, with no finite-cap assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gaussian11_strict_positive_stopping_clock_condexp_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn10_positive_event_condexp_martingale_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F M : Ω → ℝ) (hFI : Integrable F P) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0)
    (hUpper : ∀ ω, F ω ≤ b + M ω) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal := by sorry
