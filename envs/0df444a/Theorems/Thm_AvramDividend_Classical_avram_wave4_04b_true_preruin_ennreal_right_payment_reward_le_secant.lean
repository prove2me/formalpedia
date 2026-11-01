-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_true_preruin_ennreal_right_payment_reward_le_secant
-- name    : AvramDividend.Classical.avram_wave4_04b_true_preruin_ennreal_right_payment_reward_le_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:42:43.37868+00:00
-- url     : https://prove2.me/theorems/a49188f7-028c-4fee-bbdb-fba51f9776d5
-- title:
--   Actual full discounted pre-ruin right-payment reward bounded by chronological HJump secants without a real-series growth assumption
-- statement:
--   For any finite horizon and any real discount parameter, the full ENNReal countable sum of all actual chronological right-payment atoms in the true pre-ruin paymentTimes window is bounded by the corresponding full ENNReal sum of discounted HJump secants. The corrected HJump premise is needed only at time zero or strictly before the genuine ruin time. No secant-growth, finite variation of w, series integrability, or artificial all-window jump condition is assumed; the inequality remains valid even if the secant sum is infinite. This is a deterministic dividend control inequality, not an Itô–Meyer stochastic balance.
-- source:
--   04-B true pre-ruin actual source-X payment control, no Chat04 canonical UBV inequality

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_true_preruin_ennreal_right_payment_reward_le_secant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (A : Set ℝ)
    (hA : A = {s : ℝ | s ∈ paymentTimes (ruinTime X x D ω) ∧
      s ≤ (T : ℝ) ∧ 0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    (∑' s : A, ENNReal.ofReal
      (Real.exp (-(q * (s : ℝ))) *
        (rightLimit D ((s : ℝ).toNNReal) ω -
          D ((s : ℝ).toNNReal) ω))) ≤
    (∑' s : A, ENNReal.ofReal
      (Real.exp (-(q * (s : ℝ))) *
        (w (riskProcess X x D ((s : ℝ).toNNReal) ω) -
          w (riskProcess X x D ((s : ℝ).toNNReal) ω -
            (rightLimit D ((s : ℝ).toNNReal) ω -
              D ((s : ℝ).toNNReal) ω))))) := by
  sorry
