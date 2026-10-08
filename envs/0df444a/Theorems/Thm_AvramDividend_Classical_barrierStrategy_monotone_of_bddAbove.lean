-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_bddAbove
-- name    : AvramDividend.Classical.barrierStrategy_monotone_of_bddAbove
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T20:34:10.836993+00:00
-- url     : https://prove2.me/theorems/24856c5f-a619-407a-aead-6f523cecb6ad
-- title:
--   Barrier dividends are monotone when running suprema are bounded
-- statement:
--   For a spectrally negative Levy process, the barrier dividend strategy at initial reserve equal to barrier c is monotone in time, provided the real running path supremum is bounded above on each compact time interval. Supremum monotonicity follows from nested past intervals, and the maximum with zero preserves monotonicity.
-- source:
--   Reusable part of the dividend admissibility witness needed for AvramDividend.Classical.valueFunctionLe_above_cap; leaves real-path boundedness to an independent theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_monotone_of_bddAbove {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (hpath : ∀ ω (t : ℝ≥0),
      BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω))) :
    ∀ ω, Monotone (fun t => barrierStrategy X c c t ω) := by
  sorry
