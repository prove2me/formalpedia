-- Prove2me | Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
-- name    : AvramDividend.Classical.add_initial_excess_admissible_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:36:04.998991+00:00
-- url     : https://prove2.me/theorems/9edc31be-a8c7-46fb-9cd8-bcb9f5c6c8ff
-- title:
--   Add a compulsory initial excess payment to a capped dividend strategy
-- statement:
--   Conversely, take any strategy admissible from the cap c and prepend a deterministic dividend x-c at time zero by adding x-c to its strictly positive-time cumulative dividends. The resulting strategy is admissible from x under the same cap, has the same controlled reserve after time zero, and its value is x-c plus the original strategy's value.
-- source:
--   Source-neutral consequence of the formal definitions. Adding x-c to the positive-time cumulative dividend process produces an atom of mass x-c at time zero, leaves subsequent Stieltjes increments unchanged, and makes the controlled reserve started from x coincide with the original reserve started from c for every positive time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem add_initial_excess_admissible_value {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ)
    (hE : IsAdmissibleLe X c (ENNReal.ofReal c) E) :
    IsAdmissibleLe X x (ENNReal.ofReal c)
        (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ∧
      dividendValue X q x
          (fun t ω => if t = 0 then 0 else (x - c) + E t ω) =
        ENNReal.ofReal (x - c) + dividendValue X q c E := by sorry

end AvramDividend.Classical
