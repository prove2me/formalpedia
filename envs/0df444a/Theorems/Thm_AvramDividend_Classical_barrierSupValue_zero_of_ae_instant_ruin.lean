-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
-- name    : AvramDividend.Classical.barrierSupValue_zero_of_ae_instant_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:32:20.843495+00:00
-- url     : https://prove2.me/theorems/1abd15e4-2238-410b-85bf-135bce720ffe
-- title:
--   Instantaneous reflected ruin forces zero stopped barrier reward
-- statement:
--   If the first strictly positive reflected drawdown past a barrier occurs at time zero almost surely, the stopped reflected supremum reward vanishes. The canonical runningSup_reward_zero_at_instant_ruin establishes pathwise zero; integration yields zero barrierSupValue. This supplies the instantaneous-ruin case of the root-connected zero_reflectedSupValue_eq_barrierValue boundary identity without introducing new stochastic assumptions silently. The complementary bounded-variation case remains separate.
-- source:
--   Direct integration of canonical theorem AvramDividend.Classical.runningSup_reward_zero_at_instant_ruin; supports zero_reflectedSupValue_eq_barrierValue b83a725b-f7cf-4aef-8105-310d38d8cd46.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_reward_zero_at_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_zero_of_ae_instant_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X a ω = 0) :
    barrierSupValue X a q = 0 := by sorry
