-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
-- name    : AvramDividend.Classical.barrierStrategy_admissibleLe_nonnegative_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:10:53.840619+00:00
-- url     : https://prove2.me/theorems/32b4ccb8-895d-4286-937d-180d0dbe7222
-- title:
--   Any nonnegative constant barrier strategy is capped-admissible for every nonnegative initial surplus
-- statement:
--   For a spectrally negative Levy process and a nonnegative barrier a, the constant barrier strategy started from any x>=0 is admissible and keeps the controlled reserve at or below a at every positive time. When x>a the strategy removes x-a at time zero via the formal right-limit convention. This theorem is independent of the scale function and isolates the pathwise/filtration facts behind admissibility of reflected barrier policies.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Levy process, Sections 2 and 3.3, pp.3-8; source-neutral consequence of the formal barrierStrategy and admissibility definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_admissibleLe_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    IsAdmissibleLe X x (ENNReal.ofReal a) (barrierStrategy X x a) := by sorry

end AvramDividend.Classical
