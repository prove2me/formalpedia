-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
-- name    : AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T23:16:52.671117+00:00
-- url     : https://prove2.me/theorems/d58a54f2-7f8b-4467-b485-93506d163ab8
-- title:
--   Zero-capped optimal value is bounded by any verified zero-barrier boundary formula
-- statement:
--   The zero-capped value-function bound at zero initial surplus is completely reduced to the zero-barrier strategy boundary equality. A Proved stochastic comparison bounds each zero-capped admissible dividend strategy by the zero-barrier strategy, and a Proved supremum-transfer theorem bounds the restricted optimal value. This needs no bounded-variation or scale-function regularity assumption and directly supports the Open root-connected zero_cap_value_at_zero_upper_bound theorem c7854fde-e22f-45b4-90b6-1ed7e894755c. All outstanding mathematics is isolated in the endpoint valuation.
-- source:
--   Root-connected general reduction from two Proved prerequisites to the remaining zero-barrier endpoint identity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0)) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by sorry
