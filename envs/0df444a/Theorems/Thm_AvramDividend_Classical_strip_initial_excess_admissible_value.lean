-- Prove2me | Theorems.Thm_AvramDividend_Classical_strip_initial_excess_admissible_value
-- name    : AvramDividend.Classical.strip_initial_excess_admissible_value
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T22:38:17.587892+00:00
-- url     : https://prove2.me/theorems/2c817d06-09cc-4ace-84ce-8f9c54a64cd3
-- title:
--   Strip the compulsory initial excess from a capped dividend strategy
-- statement:
--   For a strategy admissible below a finite reserve cap c when started from x>c, remove the compulsory initial excess x-c from all strictly positive-time cumulative dividends while keeping D(0)=0. The resulting strategy is admissible from c under the same cap, has the same controlled reserve after time zero, and the original discounted dividend value is the deterministic initial excess plus the shifted strategy's value.
-- source:
--   Source-neutral consequence of the dividend-strategy definitions and the proved child admissibleLe_rightLimit_zero_ge_excess. The latter ensures the shifted positive-time dividend process remains nonnegative/monotone at the origin. The controlled reserve is unchanged after time zero, while the Stieltjes dividend measure loses exactly the atom of mass x-c at time zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_rightLimit_zero_ge_excess

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem strip_initial_excess_admissible_value {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    IsAdmissibleLe X c (ENNReal.ofReal c)
        (fun t ω => if t = 0 then 0 else D t ω - (x - c)) ∧
      dividendValue X q x D =
        ENNReal.ofReal (x - c) +
          dividendValue X q c
            (fun t ω => if t = 0 then 0 else D t ω - (x - c)) := by sorry

end AvramDividend.Classical
