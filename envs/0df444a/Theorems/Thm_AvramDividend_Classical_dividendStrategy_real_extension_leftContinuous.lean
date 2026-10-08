-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous
-- name    : AvramDividend.Classical.dividendStrategy_real_extension_leftContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:57:52.293496+00:00
-- url     : https://prove2.me/theorems/a994a33a-1397-4640-bdeb-6a9b5eea10df
-- title:
--   The canonical real-time extension of a dividend strategy inherits left-continuity
-- statement:
--   A dividend strategy D is pathwise left-continuous on NNReal. Its extension to real times f(s)=D(s.toNNReal) remains left-continuous at every real t: Real.toNNReal is continuous and monotone, so it maps (−∞,t] into (−∞,t.toNNReal] and the within-set composition theorem transfers D's left-continuity. This is the remaining missing continuity bridge for identifying dividendMeasure atoms with dividend right jumps.
-- source:
--   IsDividendStrategy.left_continuity; pinned Mathlib continuous_real_toNNReal, Real.toNNReal_mono and ContinuousWithinAt.comp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_real_extension_leftContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    ∀ t : ℝ,
      ContinuousWithinAt (fun s : ℝ => D s.toNNReal ω) (Iic t) t := by sorry
