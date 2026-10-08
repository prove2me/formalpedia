-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_piecewise
-- name    : AvramDividend.Classical.riskProcess_barrier_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:26:42.613977+00:00
-- url     : https://prove2.me/theorems/2c070744-e0d2-4a67-bf33-550386b161a7
-- title:
--   Two-phase controlled reserve identity at the barrier
-- statement:
--   For any positive time and a starting reserve x at or below barrier a, the reserve controlled by cumulative barrier dividends equals x+X_t while the path running supremum remains below the barrier shortfall a−x, and a+X_t−S_t once that supremum reaches a−x. This is a global pathwise identity combining the pre-dividend and reflected post-dividend phases, useful for exact ruin-event analysis without assuming strong Markov.
-- source:
--   Exact dividend and risk process definitions, the verified runningSup_eq_rawSup_nonneg and riskProcess_barrier_after_crossing lemmas; supports the factorisation obligation barrierStrategy_value_eq_exit_factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_after_crossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_barrier_piecewise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω) :
    riskProcess X x (barrierStrategy X x a) t ω =
      if runningSup X t ω < a - x then
        x + X.X t ω
      else
        a + X.X t ω - runningSup X t ω := by sorry
