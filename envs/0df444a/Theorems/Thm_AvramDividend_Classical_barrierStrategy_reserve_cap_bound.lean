-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound
-- name    : AvramDividend.Classical.barrierStrategy_reserve_cap_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T18:55:26.759069+00:00
-- url     : https://prove2.me/theorems/e04214f3-0b78-477c-b73a-1a50c04ace82
-- title:
--   Barrier strategy respects the reserve cap at positive times
-- statement:
--   For any spectrally negative Lévy process, starting at reserve c and using the barrier dividend strategy at c produces a reserve at or below c at each positive time, in the extended nonnegative real cap convention. This follows because the running supremum of X up to time t is at least X_t.
-- source:
--   Algebraic cap bound of the Avram classical dividend mission using definitions of barrierStrategy and riskProcess; no process-regularity or analytic assumptions. Immutable proof SHA256 dd153af57258e45da1cdbdfc5517d2a0bfdb06cc2b2bbbf4dd1cdedb4b796f49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_reserve_cap_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      ENNReal.ofReal (riskProcess X c (barrierStrategy X c c) t ω) ≤
        ENNReal.ofReal c := by
  sorry
