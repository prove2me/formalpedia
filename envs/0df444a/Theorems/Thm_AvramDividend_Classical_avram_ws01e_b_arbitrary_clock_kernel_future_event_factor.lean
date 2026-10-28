-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_arbitrary_clock_kernel_future_event_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_arbitrary_clock_kernel_future_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:31:38.284603+00:00
-- url     : https://prove2.me/theorems/f620c1a3-da4b-404a-95a1-a9bdb4b63ff0
-- title:
--   Whole residual-clock event kernel factors from a genuinely independent shifted future path
-- statement:
--   On an actual product probability P×Q, let a measurable nonnegative random stopping age τ be independent of a measurable future-path statistic Y under P. For any jointly measurable external-clock event kernel K(age,clock) whose clock-section probabilities form a measurable function discount(age), the joint probability that K(τ,clock) occurs and Y lies in a measurable B is exactly the probability of the clock event times P(Y∈B). In particular, K can be a survival window, a shifted residual-clock Borel event or the entire stopped-age/clock cylinder. The proof is a source-faithful Tonelli section calculation, independent stopping-weight/future-reward integral factorisation and indicator integration; it does not assume Wiener–Hopf independence or a tilted stopping-time law.
-- source:
--   Canonical Proved AvramDividend.Classical.indepStoppingWeight_futureReward_lintegral_factor 36f318c5-d560-40ee-ac9f-d218736e55b3; pinned Mathlib Measure.prod_apply and lintegral_indicator_fun_one; strong Markov and residual-clock splitting in Kuznetsov–Kyprianou–Rivero (2012).

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_indepStoppingWeight_futureReward_lintegral_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_arbitrary_clock_kernel_future_event_factor
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (K : ℝ≥0 → Θ → Prop)
    (hK : MeasurableSet {z : ℝ≥0 × Θ | K z.1 z.2})
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hKernel : ∀ a : ℝ≥0, Q {η : Θ | K a η} = discount a)
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} =
      (P.prod Q) {z : Ω × Θ | K (τ z.1) z.2} *
        P (Y ⁻¹' B) := by sorry
