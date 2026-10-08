-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
-- name    : AvramDividend.Classical.barrierStrategy_reserve_cap_bound_all_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:13:16.162095+00:00
-- url     : https://prove2.me/theorems/19cf2851-5764-47cf-88d1-681eaeded9e5
-- title:
--   The controlled reserve under a nonnegative barrier never exceeds the barrier
-- statement:
--   For any x>=0 and nonnegative barrier a, after time zero the reserve process controlled by barrierStrategy is at most a. If the running supremum has triggered reflection, the reserve is a plus X_t minus its running supremum and is <=a; otherwise the defining inequality for the inactive positive part gives the same bound. For x>a the initial excess is removed immediately by the right-limit convention.
-- source:
--   Source-neutral pathwise consequence of the barrierStrategy and riskProcess definitions; corresponds to reflection below the constant barrier in Avram, Palmowski and Pistorius (2007), Section 3.3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_reserve_cap_bound_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    ∀ ω (t : ℝ≥0), 0 < t →
      ENNReal.ofReal (riskProcess X x (barrierStrategy X x a) t ω) ≤ ENNReal.ofReal a := by sorry

end AvramDividend.Classical
