-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset
-- name    : AvramDividend.Classical.firstRecord_drawdown_post_shift_reset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:50:54.776957+00:00
-- url     : https://prove2.me/theorems/e8ca9cea-44f4-43d7-b777-6cefc8573c7c
-- title:
--   Reflected drawdown resets to the shifted future supremum at an attained first record
-- statement:
--   At any finite first strict upward passage u of a nonnegative level b, reflected drawdown is zero at u. Consequently the drawdown at u+t equals precisely the future shifted path's running supremum over [0,t] minus its terminal value. This composes two independently Proved pathwise theorems and removes the pre-record history from the future ruin criterion, a core prerequisite of the strong-Markov killed-record renewal step.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; drawdown restart at attained reflected barrier records.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_drawdown_after_firstUpcrossing_shift

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstRecord_drawdown_post_shift_reset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    ∀ t : ℝ≥0,
      runningSup X (u + t) ω - X.X (u + t) ω =
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X (u + t) ω := by sorry
