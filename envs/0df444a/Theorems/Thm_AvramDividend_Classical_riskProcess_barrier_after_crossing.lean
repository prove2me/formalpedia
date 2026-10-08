-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_after_crossing
-- name    : AvramDividend.Classical.riskProcess_barrier_after_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:40:48.303698+00:00
-- url     : https://prove2.me/theorems/3eca7767-d9e6-4c9d-a596-667cbc2287b3
-- title:
--   After the first barrier crossing, controlled reserves are barrier minus reflected drawdown
-- statement:
--   After the past running supremum has reached the initial shortfall a−x at any positive time, the barrier dividend strategy has cumulatively paid x−a+S_t, and its controlled risk process is U_t=a+X_t−S_t. This is the exact pathwise post-first-passage reflection identity in the strong-Markov barrier-value argument, without using any deprecated stopping-time definitions.
-- source:
--   Definition of riskProcess and barrierStrategy, runningSup, and the accepted runningSup_eq_rawSup_nonneg theorem. Elementary max-zero and subtraction algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_barrier_after_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω)
    (hcross : a - x ≤ runningSup X t ω) :
    riskProcess X x (barrierStrategy X x a) t ω =
      a + X.X t ω - runningSup X t ω := by sorry
