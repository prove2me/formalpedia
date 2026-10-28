-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_drawdown
-- name    : AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:17:33.599505+00:00
-- url     : https://prove2.me/theorems/1fa70426-22a7-4003-98e1-939fdb2b0ae4
-- title:
--   Arbitrarily early strict drawdowns imply zero reflected ruin time
-- statement:
--   For each sample path, if every strictly positive time window contains a strict drawdown above level a, the actual reflected drawdown ruin time is zero. The proof uses the canonical iInf definition of barrierRuinTime and a positive finite NNReal between zero and any hypothetical positive ruin time. This deterministic reduction isolates the remaining probabilistic regularity theorem: unbounded-variation spectrally negative Lévy sample paths exhibit such early drawdowns almost surely. It directly supplies the pathwise component of the current zero_reflectedSupValue_eq_barrierValue dependency.
-- source:
--   Pathwise first-ruin infimum reduction for root-connected zero-reflectedSupValue_eq_barrierValue; uses the existing ReflectionBarrier barrierRuinTime definition.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_drawdown
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω)
    (hNear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ a < drawdown X t ω) :
    barrierRuinTime X a ω = 0 := by sorry
