-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_payment_feasible_nonnegative_barrier
-- name    : AvramDividend.Classical.barrierStrategy_payment_feasible_nonnegative_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:41:34.008869+00:00
-- url     : https://prove2.me/theorems/94fda3cd-cda4-4838-8997-83cbb6262b37
-- title:
--   Barrier-strategy dividend jumps never exceed the available reserve
-- statement:
--   For the constant barrier strategy at a nonnegative barrier, every dividend lump paid at time t is at most the reserve immediately before that payment, including the formal time-zero convention. Pathwise this follows from reflection at the running maximum: increases in cumulative dividends occur only when the uncontrolled surplus would exceed the barrier, and the payment removes exactly the available excess. This is the payment-feasibility conjunct of IsAdmissible, isolated from regularity/adaptedness and from the reserve-cap claim.
-- source:
--   Avram, Palmowski and Pistorius (2007), Sections 2 and 3.3; pathwise admissibility of reflection at a constant barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_payment_feasible_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω) →
        rightLimit (barrierStrategy X x a) t ω -
            barrierStrategy X x a t ω ≤
          riskProcess X x (barrierStrategy X x a) t ω := by sorry

end AvramDividend.Classical
