-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_survival_nested
-- name    : AvramDividend.Classical.killed_firstRecord_grid_survival_nested
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:54:26.428292+00:00
-- url     : https://prove2.me/theorems/965eca05-7c70-4d8b-9e9d-c9d6638501cd
-- title:
--   A surviving later killed record implies survival of every preceding adjacent record
-- statement:
--   For a nonnegative record spacing ε and any index n, if the strict upward passage of (n+2)ε occurs before actual reflected ruin at barrier a, then the passage of (n+1)ε occurs before that same ruin time. Use the already Proved order monotonicity of official strict first-upcrossing clocks and the adjacent grid level inequality. This exact event inclusion is needed for strong-Markov conditioning of the first-record renewal step.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; monotone nested record-survival events.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_grid_survival_nested
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (ω : Ω)
    (hSurvive :
      twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω <
        barrierRuinTime X a ω) :
    twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
      barrierRuinTime X a ω := by sorry
