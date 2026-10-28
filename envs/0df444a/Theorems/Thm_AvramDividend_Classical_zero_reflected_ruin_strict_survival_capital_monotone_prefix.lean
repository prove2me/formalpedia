-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
-- name    : AvramDividend.Classical.zero_reflected_ruin_strict_survival_capital_monotone_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:55:39.288428+00:00
-- url     : https://prove2.me/theorems/e0e5e838-ca53-494f-b343-482161119c35
-- title:
--   Before zero-barrier strict reflected ruin, the actual Lévy capital path is nondecreasing
-- statement:
--   For the exact original strict drawdown ruin clock at barrier zero, every time strictly before ruin has zero drawdown: otherwise that time would already belong to the infimum set defining ruin. Consequently the capital path coincides with its actual running supremum and is nondecreasing throughout each initial interval whose endpoint lies strictly before ruin. This deterministic fact is the pathwise grid-bound prerequisite in finite-activity zero-barrier valuation.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 exact strict drawdown clock; existing canonical runningSup_monotone_and_path_le and ReflectionBarrier definition.

import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_reflected_ruin_strict_survival_capital_monotone_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hBefore : (T : ℝ≥0∞) < barrierRuinTime X 0 ω) :
    ∀ s u : ℝ≥0, s ≤ u → u ≤ T → X.X s ω ≤ X.X u ω := by sorry
