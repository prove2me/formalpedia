-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:16:15.12781+00:00
-- url     : https://prove2.me/theorems/33663233-630e-4e02-850a-a779961f47b8
-- title:
--   Barrier dividends are right-continuous
-- statement:
--   The constant-barrier dividend process started at its barrier is pathwise right-continuous. Identify it with the running supremum, then apply the generic right-continuity theorem for running suprema to the right-continuous Levy sample path.
-- source:
--   Barrier admissibility regularity bridge. Publication must wait until all imported support theorems are canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_right_continuous {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Ici t) t := by
  sorry
