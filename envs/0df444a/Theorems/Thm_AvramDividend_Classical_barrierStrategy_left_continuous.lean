-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_left_continuous
-- name    : AvramDividend.Classical.barrierStrategy_left_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:15:52.341185+00:00
-- url     : https://prove2.me/theorems/61a2636f-cc3a-46fc-9fd7-605557de888e
-- title:
--   Barrier dividends are left-continuous
-- statement:
--   The constant-barrier dividend process started at its barrier is pathwise left-continuous. Identify it with the running supremum. At positive times the running supremum has no upward jump because X has a finite left limit and X_t does not exceed that limit; at time zero left continuity is trivial on the lower endpoint.
-- source:
--   Barrier admissibility regularity bridge. Publication must wait until all imported support theorems are canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_left_continuous {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Iic t) t := by
  sorry
