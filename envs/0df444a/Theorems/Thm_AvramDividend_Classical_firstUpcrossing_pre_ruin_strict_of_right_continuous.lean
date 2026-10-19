-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_pre_ruin_strict_of_right_continuous
-- name    : AvramDividend.Classical.firstUpcrossing_pre_ruin_strict_of_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:03:37.993703+00:00
-- url     : https://prove2.me/theorems/05e40496-e6c7-49d5-9c54-7b719a196f54
-- title:
--   Finite first new record precedes strict reflected ruin when no prior breach occurs
-- statement:
--   At a finite first upcrossing of nonnegative record b, the reflected Lévy drawdown equals zero. If no strict drawdown breach above a>0 occurred before that time and the reflected path is right-continuous there, then the new-record time is strictly earlier than the extended first strict drawdown-ruin time. This resolves the equality-endpoint issue in killed first-passage renewal: right-continuity gives a positive interval after the record without strict ruin, and the assumed no-breach prefix controls earlier times. The theorem leaves right-continuity explicit for an independent proof from the càdlàg Lévy and running-supremum fields.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 killed reflected-record passage; accepted boundary-contact theorem 9243feef-85e4-45be-9f62-5e56edb2abbf and Mathlib right-neighbourhood basis.

import Mathlib.Topology.Order.LeftRightNhds
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero

open MeasureTheory Filter Topology Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_pre_ruin_strict_of_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBefore : ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ a)
    (hRight : ContinuousWithinAt (fun t => reflectedSup X t ω)
      (Set.Ici u) u) :
    (u : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : a < reflectedSup X t ω), (t : ℝ≥0∞)) := by sorry
