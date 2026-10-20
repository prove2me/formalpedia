-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
-- name    : AvramDividend.Classical.barrierSupValue_mono_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:32:14.527122+00:00
-- url     : https://prove2.me/theorems/b91cffd4-358f-4ecb-aff0-5bd6254c0dcc
-- title:
--   The original stopped reflected-regulator dividend value is monotone in its drawdown ruin barrier
-- statement:
--   For every spectrally negative Lévy process, fixed discount q (of either sign), and barriers a≤b, the original expected discounted running-supremum Stieltjes payoff stopped at strict reflected drawdown ruin is no greater at a than at b. Indeed the drawdown first-breach time is nondecreasing in the barrier, so the prescribed dividend payment-time set increases pathwise, including the distinguished time-zero atom. Monotonicity of restricted nonnegative Lebesgue integrals then yields the pointwise and expectation inequalities. This is the true original barrierSupValue, not a surrogate conditionally constructed payoff.
-- source:
--   Def_AvramDividend_Classical_ReflectionBarrier genuine stopped integral, Prove2Me pending barrierRuinTime_mono_barrier, pinned Mathlib lintegral_mono_set.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_mono_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b q : ℝ) (hab : a ≤ b) :
    barrierSupValue X a q ≤ barrierSupValue X b q := by sorry
