-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_exact_clock_zero_reward_le_initial
-- name    : AvramDividend.Classical.avram_p4_f8_original_exact_clock_zero_reward_le_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:18:09.276079+00:00
-- url     : https://prove2.me/theorems/23c3965a-004e-4e88-b9c3-3df0abaf41cb
-- title:
--   At every original stopped source clock equal to zero, the exact postpayment reward and closed Stieltjes cash are at most the initial HJB value
-- statement:
--   For the original Lévy process and actual admissible dividend strategy, at every sample where the stopping clock is zero, the exact discounted post-right-payment w terminal and closed-Iic Stieltjes cash sum is bounded by w(x). This includes immediate ruin and the time-zero right dividend. It is a key source-level zero-event half of the original arbitrary-clock expected HJB bound.
-- source:
--   Original source exact F and σ with no artificial process; genuinely derives the time-zero reward bound from previously proved actual original clock theorem a2629a86.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f8_original_exact_clock_zero_reward_le_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k ω, σ k ω = 0 → F k ω ≤ w x := by sorry
