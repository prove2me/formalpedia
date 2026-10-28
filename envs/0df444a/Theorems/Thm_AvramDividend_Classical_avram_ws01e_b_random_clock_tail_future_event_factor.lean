-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_clock_tail_future_event_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_random_clock_tail_future_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:20:03.756441+00:00
-- url     : https://prove2.me/theorems/48753cde-ea9d-4299-95c2-dbde801b80d7
-- title:
--   Independent observation clock: survival to a random stopping age factors from a future-path event
-- statement:
--   Suppose a nonnegative random stopping age τ and a measurable future-path statistic Y are genuinely independent under a process probability P. On a separate independent observation-clock space Q, assume the clock is measurable and has measurable strict survival kernel Q(e>a)=discount(a) for every nonnegative a. Then the joint probability that the clock survives τ and Y lies in any measurable event B is exactly the survival-to-τ probability multiplied by the marginal probability of B. The conclusion concerns the actual shared future-path statistic and strict random-clock event under P×Q, without assuming the desired fluctuation factorisation. The proof is Tonelli's section formula followed by the previously verified independent-stopping-time discounted-future-reward factorisation.
-- source:
--   Mathlib MeasureTheory.Measure.prod_apply and MeasureTheory.lintegral_indicator_fun_one; accepted AvramDividend.Classical.indepStoppingWeight_futureReward_lintegral_factor 36f318c5-d560-40ee-ac9f-d218736e55b3; Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes with Applications, exponential-horizon splitting at the supremum.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_indepStoppingWeight_futureReward_lintegral_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_random_clock_tail_future_event_factor
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B} =
      (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} * P (Y ⁻¹' B) := by sorry
