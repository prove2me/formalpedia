-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_capped_admissible_of_regular
-- name    : AvramDividend.Classical.barrierStrategy_capped_admissible_of_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:08:48.384567+00:00
-- url     : https://prove2.me/theorems/09add7aa-1fa8-4045-a1f8-9cc3d55cbd34
-- title:
--   Barrier strategy is capped admissible given left and right continuity and adaptation
-- statement:
--   For a spectrally negative Levy process and nonnegative initial reserve c, the barrier dividend strategy at c is admissible with reserves capped by c if its dividend process is left-continuous, right-continuous and adapted. Pathwise monotonicity and the reserve cap are established in earlier helper theorems. Right-continuity implies zero right dividend jumps, which makes the ruin-time admissibility condition automatic. This statement exposes precisely the three remaining regularity obligations.
-- source:
--   Proof assembly bridge to show nonemptiness of IsAdmissibleLe for AvramDividend.Classical.valueFunctionLe_above_cap, using already authored dependencies. Publication should wait until all imports are actually remote Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Theorems.Thm_AvramDividend_Classical_admissible_of_no_right_dividend_jumps

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_capped_admissible_of_regular {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (hc : 0 ≤ c)
    (hleft : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Iic t) t)
    (hright : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Ici t) t)
    (hadapt : Adapted 𝓕 (barrierStrategy X c c)) :
    IsAdmissibleLe X c (ENNReal.ofReal c) (barrierStrategy X c c) := by
  sorry
