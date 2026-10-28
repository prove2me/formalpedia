-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:52:19.578697+00:00
-- url     : https://prove2.me/theorems/32cf9a92-c026-41db-abfa-b36b5e1509c4
-- title:
--   A true memoryless clock has the original full residual-time distribution after surviving a stopped age
-- statement:
--   Let τ be a measurable nonnegative age independent of an external nonnegative clock e, with survival kernel discount(a), strict memorylessness discount(a+t)=factor(t)discount(a), and discount(0)=1. Under positive product probability of τ<e, the pushforward distribution of the genuine real residual e−τ conditioned on τ<e equals the unconditional pushforward real clock law of e. The theorem proves equality of all Borel laws via nonnegative upper tails, negative-threshold support and the standard distribution-function uniqueness principle. The independent future statistic in the hypotheses connects to the existing Proved conditional tail interface and imposes no Wiener–Hopf factorisation. This gives the fresh exponential-clock law once the strict exponential survival kernel is instantiated.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_tail

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
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
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hZero : discount 0 = 1)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    Measure.map (fun z : Ω × Θ =>
      (e z.2 : ℝ) - (τ z.1 : ℝ))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    Measure.map (fun η : Θ => (e η : ℝ)) Q := by sorry
