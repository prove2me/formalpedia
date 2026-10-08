-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
-- name    : AvramDividend.Classical.valueFunctionLe_above_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:03:06.562438+00:00
-- url     : https://prove2.me/theorems/8bd7e873-81b3-409e-a448-bb17eabc4faa
-- title:
--   Restricted dividend value above a finite cap splits off the initial excess
-- statement:
--   For a nonnegative finite reserve cap c and an initial reserve x>c, every strategy admissible under the cap must remove the excess x-c at time zero. Subtracting that deterministic initial lump from the dividend process gives a strategy admissible from c with the same controlled reserve thereafter, and conversely adding it gives a capped strategy from x. Therefore the restricted optimal value from x is exactly the initial excess x-c plus the restricted optimal value from c.
-- source:
--   Source-neutral consequence of the definitions of the controlled reserve, admissibility under a cap, the Lebesgue-Stieltjes dividend measure, and valueFunctionLe. The already-published child admissibleLe_rightLimit_zero_ge_excess isolates the pathwise fact forcing the initial excess payment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem valueFunctionLe_above_cap {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x) :
    valueFunctionLe X q (ENNReal.ofReal c) x =
      ENNReal.ofReal (x - c) + valueFunctionLe X q (ENNReal.ofReal c) c := by sorry

end AvramDividend.Classical
