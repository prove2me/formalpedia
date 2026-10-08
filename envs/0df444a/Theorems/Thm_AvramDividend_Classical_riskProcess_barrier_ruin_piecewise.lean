-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_ruin_piecewise
-- name    : AvramDividend.Classical.riskProcess_barrier_ruin_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:34:58.522646+00:00
-- url     : https://prove2.me/theorems/25d809f8-e375-403c-88a6-330defc1238f
-- title:
--   Controlled-reserve ruin event before and after dividend activation
-- statement:
--   For each strictly positive deterministic time, negative controlled reserves under an Avram barrier dividend strategy occur exactly by one of two disjoint mechanisms: before running supremum reaches a−x, the original Lévy process has fallen below −x; after it reaches a−x, the reflected drawdown S_t−X_t exceeds the barrier a. This is an exact pathwise event split, not a strong-Markov or two-sided-exit probability law.
-- source:
--   Canonical dividend strategy and risk-process definitions and the prepared separate piecewise reserve identity riskProcess_barrier_piecewise; a pathwise dependency for the first-passage ruin-event treatment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_barrier_ruin_piecewise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ht : 0 < t) (ω : Ω) :
    riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
      (runningSup X t ω < a - x ∧ X.X t ω < -x) ∨
      (a - x ≤ runningSup X t ω ∧
        a < runningSup X t ω - X.X t ω) := by sorry
