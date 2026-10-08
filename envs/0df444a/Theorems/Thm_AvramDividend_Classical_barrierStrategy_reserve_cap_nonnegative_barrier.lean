-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_nonnegative_barrier
-- name    : AvramDividend.Classical.barrierStrategy_reserve_cap_nonnegative_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:42:39.503798+00:00
-- url     : https://prove2.me/theorems/bbe340d9-8131-47bc-82b5-ba6881cd7500
-- title:
--   Reflection at a nonnegative barrier keeps the positive-time reserve below the barrier
-- statement:
--   For every positive time t, the controlled reserve under the constant barrier strategy is at most the barrier a. The running supremum in the dividend process dominates the current Levy value and contains X_0=0; subtracting the reflected dividend therefore leaves reserve at most a. This is exactly the cap conjunct required for membership of Pi_{<=a}.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.3; pathwise reflection at the constant upper barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_reserve_cap_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    ∀ ω (t : ℝ≥0), 0 < t →
      ENNReal.ofReal (riskProcess X x (barrierStrategy X x a) t ω) ≤
        ENNReal.ofReal a := by sorry

end AvramDividend.Classical
