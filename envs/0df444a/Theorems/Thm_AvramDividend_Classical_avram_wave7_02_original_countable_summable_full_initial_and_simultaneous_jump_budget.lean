-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_countable_summable_full_initial_and_simultaneous_jump_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_countable_summable_full_initial_and_simultaneous_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:47:30.925365+00:00
-- url     : https://prove2.me/theorems/ff895062-6299-46a9-872a-971229989b82
-- title:
--   Original complete initial Stieltjes and countable summable concurrent source-and-dividend jump HJB budget
-- statement:
--   Actual source-specific countable summable simultaneous original negative Levy jumps and right-dividend payments have a nonpositive discounted correction across ruin, with the original time-zero right-payment value budget kept explicitly. This is a pathwise lemma under explicit summability and chronological source-before-payment HJB hypotheses, not the stopped stochastic Ito or compensation identity.
-- source:
--   Follow-up from W7-02 Proved original source weak C1 negative mark all crossings, simultaneous jump chronological HJB budget and original initial dividendMeasure singleton theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_countable_summable_full_initial_and_simultaneous_jump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hTimes : ∀ n, 0 < t n ∧ (t n : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ n,
      X.X (t n) ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω) ≤ C)
    (hSummable : Summable (fun n : ℕ =>
      Real.exp (-(q * (t n : ℝ))) *
        ((w (x + X.X (t n) ω - rightLimit D (t n) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) -
              D (t n) ω)) +
          (rightLimit D (t n) ω - D (t n) ω)))) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑' n : ℕ,
        Real.exp (-(q * (t n : ℝ))) *
          ((w (x + X.X (t n) ω - rightLimit D (t n) ω) -
              w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) -
                D (t n) ω)) +
            (rightLimit D (t n) ω - D (t n) ω))) ≤ w x := by sorry
