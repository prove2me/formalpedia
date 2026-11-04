-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_right_tendsto_to_continuousWithinAt_Ici
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_right_tendsto_to_continuousWithinAt_Ici
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:17:51.607241+00:00
-- url     : https://prove2.me/theorems/4191636d-2f21-4bd3-a7a6-49463ea2b7d9
-- title:
--   Strict-right convergence on NNReal entails closed-right continuity for Stieltjes construction
-- statement:
--   A real-valued path on nonnegative real time with its strict-right limit equal to its current value is continuous within the closed right time cone Ici t. The proof splits the closed-right neighbourhood into strict-right and singleton filters using the pinned Mathlib filter identity. This supplies the exact StieltjesFunction constructor continuity hypothesis for the original cumulative jump path.
-- source:
--   Pinned Mathlib nhdsGT_sup_nhdsWithin_singleton, Filter.map_sup, nhdsWithin_singleton and tendsto_pure_nhds as verified by accepted original zero-time continuity proof 56ed0b8e...

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_a_bvdrift_right_tendsto_to_continuousWithinAt_Ici
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hright : Filter.Tendsto f (𝓝[>] t) (𝓝 (f t))) :
    ContinuousWithinAt f (Ici t) t := by sorry
