-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_of_bddAbove
-- name    : AvramDividend.Classical.barrierStrategy_reserve_cap_bound_of_bddAbove
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T20:17:14.631991+00:00
-- url     : https://prove2.me/theorems/8a03fb7b-e89b-4e9b-98c1-cb2be148b294
-- title:
--   Barrier reserve cap bound assuming a bounded path supremum
-- statement:
--   A barrier strategy at starting level c has reserves bounded above by c at every positive time provided the underlying path on the time interval up to that time is bounded above. The cap follows from the finite real supremum over past process values. The separate remaining process-regularity obligation is to prove boundedness of paths on compact time intervals.
-- source:
--   Direct order-theoretic bridge to Avram Dividend cap theorem e04214f3-0b78-477c-b73a-1a50c04ace82, isolating cadlag-path boundedness from sup comparison.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_reserve_cap_bound_of_bddAbove {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω)) →
      ENNReal.ofReal (riskProcess X c (barrierStrategy X c c) t ω) ≤
        ENNReal.ofReal c := by
  sorry
