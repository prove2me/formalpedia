-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_shifted_ruin_window
-- name    : AvramDividend.Classical.barrierStrategy_stoppedReward_shifted_ruin_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:31:57.071736+00:00
-- url     : https://prove2.me/theorems/b3933be6-8979-48a7-891d-8e4eb67dab3a
-- title:
--   Exact stopped barrier payoff restarts with the ruin clock of future Lévy increments
-- statement:
--   If a finite first upper barrier passage u precedes controlled ruin, the full stopped discounted barrier dividend reward equals exp(-qu) times the discounted post-u shifted Lévy running-supremum Stieltjes reward stopped by the first future time at which the shifted reflected reserve becomes negative. The original random payment window is replaced by an explicit functional of the shifted increment path, with no extra measure support hypotheses. This is the precise pathwise prerequisite for the strong-Markov barrier value factorisation.
-- source:
--   Composes proved barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy 5b38749e, actual shifted ruin clock 609e34dd, and translated_payment_window_eq_shifted_ruin_window 4d86d04a. Main factorisation parent 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
import Theorems.Thm_AvramDividend_Classical_translated_payment_window_eq_shifted_ruin_window
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_stoppedReward_shifted_ruin_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hsuccess : (u : ℝ≥0∞) <
      ruinTime X x (barrierStrategy X x a) ω) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂dividendMeasure (barrierStrategy X x a) ω) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in (Set.Ioi (0 : ℝ)) ∩
        paymentTimes (⨅ (r : ℝ≥0)
          (_ : a + (X.X (u + r) ω - X.X u ω) <
            max 0
              (sSup ((fun z : ℝ≥0 => X.X (u + z) ω) '' Set.Icc 0 r) -
                X.X u ω)), (r : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun r (_ : Ω) =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω)) := by sorry
