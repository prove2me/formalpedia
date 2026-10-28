-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_expected_record_sum_finite_ae
-- name    : AvramDividend.Classical.chat12_expected_record_sum_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:28:13.390224+00:00
-- url     : https://prove2.me/theorems/d0c270ad-cacf-47a7-bfd5-64842ea607dc
-- title:
--   Almost-everywhere finiteness of record-payment sums from expected rewards
-- statement:
--   For measurable nonnegative extended-real rewards w_n on any measure space, if the sum over n of their Lebesgue integrals is finite, then almost every sample path has a finite sum of rewards. This is a Tonelli-based bridge between the proved expected killed-record geometric bound and Chat 5's pathwise dividend-measure arguments, not a proof of the dividend measure estimate itself.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_expected_record_sum_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, Measurable (w n))
    (hbound : (∑' n : ℕ, ∫⁻ ω, w n ω ∂P) < ∞) :
    ∀ᵐ ω ∂P, (∑' n : ℕ, w n ω) < ∞ := by sorry
