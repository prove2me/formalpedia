-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_ruin_iff_drawdown_after_crossing
-- name    : AvramDividend.Classical.barrier_ruin_iff_drawdown_after_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T20:30:34.714036+00:00
-- url     : https://prove2.me/theorems/6026b125-b785-4675-8b40-2a0ede15167d
-- title:
--   After barrier passage, ruin is exactly reflected drawdown exceeding the barrier
-- statement:
--   Once the running supremum has reached the initial barrier shortfall, the controlled reserves are a plus the current Lévy increment minus the running supremum. Therefore at each positive time after crossing, controlled ruin occurs exactly when the drawdown of the Lévy path from its running maximum exceeds the barrier a. This is the post-passage pathwise ruin-time equivalence needed to align the discounted dividend reward with the reflected drawdown stopping event.
-- source:
--   The already-Proved AvramDividend.Classical.riskProcess_barrier_after_crossing identity and the canonical runningSup/riskProcess definitions, in the pathwise phase of AvramDividend.Classical.barrierStrategy_value_eq_exit_factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrier_ruin_iff_drawdown_after_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω)
    (hcross : a - x ≤ runningSup X t ω) :
    (riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
      a < runningSup X t ω - X.X t ω) := by sorry
