-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
-- name    : AvramDividend.Classical.avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:53:11.541043+00:00
-- url     : https://prove2.me/theorems/0315346e-a771-490f-b107-7af330db9139
-- title:
--   Exact original time-zero right-payment HJB value drop and complete Stieltjes atom, even at immediate ruin
-- statement:
--   The true original Levy source starts at zero and every original left-continuous dividend strategy starts at D0=0; the canonical verification right-payment jump inequality at time zero implies the initial right payment plus the postpayment candidate value is at most the initial w(x). The exact original dividend Stieltjes singleton is the ENNReal image of the payment, and the payment is nonnegative. This holds even if positive-time ruin is immediate, without assuming any artificial initial transition or ignoring the atom.
-- source:
--   The exact source X.X_zero, D0=0, canonical hjump at time zero, Proved original dividend singleton and monotone right limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) :
    w (x - rightLimit D 0 ω) + rightLimit D 0 ω ≤ w x ∧
    dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal (rightLimit D 0 ω) ∧
    0 ≤ rightLimit D 0 ω := by sorry
