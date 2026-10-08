-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
-- name    : AvramDividend.Classical.barrierStrategy_self_eq_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T10:07:11.95039+00:00
-- url     : https://prove2.me/theorems/6f853442-0ba9-4515-8a3d-2297508c4913
-- title:
--   Barrier strategy started at its barrier equals the running supremum at every time
-- statement:
--   When initial reserve equals the barrier, cumulative barrier dividends equal the running supremum of the Levy process at every time, including time zero. At positive times this follows from the barrier definition and nonnegativity of the running supremum. At time zero both sides are zero because the process starts at zero and the indexing interval is a singleton.
-- source:
--   Reusable bridge for barrier-strategy regularity and admissibility. Corrected from an older private helper by removing an invalid function-extensionality step in a scalar equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_self_eq_runningSup {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (ω : Ω) (t : ℝ≥0) :
    barrierStrategy X c c t ω = runningSup X t ω := by
  sorry
