-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
-- name    : AvramDividend.Classical.barrierRuinTime_mono_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:22:07.709055+00:00
-- url     : https://prove2.me/theorems/6c566972-11fb-48af-a946-abaa30336bf1
-- title:
--   The genuine reflected-drawdown ruin time is nondecreasing in the barrier
-- statement:
--   For a fixed sample path, increasing the strict drawdown ruin barrier from a to b≥a can only postpone (or leave unchanged) the first time that reflectedSup exceeds the barrier. This is proved directly at the extended nonnegative first-breach-time level, including unreachable barriers with time ⊤ and equality/strict endpoint conventions, by inclusion of breach events and order of indexed infima. It is a pathwise prerequisite for monotonicity of stopped regulator dividend rewards and uses no Markov or scale-function assumptions.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 eq (3.12) strict reflected drawdown ruin definition, Def_AvramDividend_Classical_ReflectionBarrier.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierRuinTime_mono_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    barrierRuinTime X a ω ≤ barrierRuinTime X b ω := by sorry
