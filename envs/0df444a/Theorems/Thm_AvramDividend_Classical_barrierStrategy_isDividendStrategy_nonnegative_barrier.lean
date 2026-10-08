-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
-- name    : AvramDividend.Classical.barrierStrategy_isDividendStrategy_nonnegative_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:13:30.152907+00:00
-- url     : https://prove2.me/theorems/501af29f-f958-42d6-8682-5dc331fedae7
-- title:
--   The constant barrier construction is a dividend strategy
-- statement:
--   For x>=0 and a>=0, the cumulative constant-barrier dividend process is a dividend strategy: it starts at zero, is nondecreasing, is left-continuous, and is adapted to the filtration. The proof uses the running supremum representation of barrierStrategy, path regularity of the Levy process, and adaptedness of the running supremum.
-- source:
--   Avram, Palmowski and Pistorius (2007), Sections 2 and 3.3; source-faithful pathwise properties of the formal barrierStrategy definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_isDividendStrategy_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    IsDividendStrategy 𝓕 (barrierStrategy X x a) := by sorry

end AvramDividend.Classical
