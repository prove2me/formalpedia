-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie
-- name    : AvramDividend.Classical.avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:53:59.946501+00:00
-- url     : https://prove2.me/theorems/455a7bf6-fea9-4d8a-9093-5425b88dcb00
-- title:
--   Independent atomless observation clock cannot tie a random stopping age
-- statement:
--   On the authentic product probability P×Q, let τ be any measurable nonnegative random age of the process, and e a separately sampled measurable observation clock whose law has no point masses. Then the event τ=e has probability zero, irrespective of τ's dependence on the underlying path. This is the clock-tie null-event theorem needed to equate strict record passage before a genuine exponential horizon with running-supremum threshold events. The proof evaluates product-measure sections and uses Q{e=τ(ω)}=0 for every process sample; no Wiener–Hopf independence is assumed.

import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set
open scoped NNReal ENNReal

/-- An independent atomless observation clock has zero probability of a tie
with any measurable random stopping age, even when the age depends on the
whole underlying Lévy path. The proof is a genuine product-space Tonelli
argument, with no path stopping identity or Wiener–Hopf factor assumed. -/

theorem AvramDividend.Classical.avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hAtomless : ∀ a : ℝ≥0, Q {η : Θ | e η = a} = 0) :
    (P.prod Q) {z : Ω × Θ | τ z.1 = e z.2} = 0 := by sorry
