-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital_of_boundary
-- name    : AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:45:45.41681+00:00
-- url     : https://prove2.me/theorems/e6bc8ce5-2abf-47fe-87e0-ad213195b802
-- title:
--   Complete zero-barrier valuation for every reserve from a single boundary equality
-- statement:
--   The zero-barrier strategy value formula for every nonnegative initial reserve is completely reduced to the boundary value formula at reserve zero and its real nonnegativity. The zero reserve case is exactly the supplied hypothesis. For positive reserves use the canonically Proved theorem barrierStrategy_above_value_of_boundary, which already handles the immediate initial lump sum and the affine scale-function formula. This works in both bounded and unbounded variation, and directly supports the Open root prerequisite barrier_strategy_value_zero_all_capital (d73a6aec-f808-4bc8-935d-5004c5b67597).
-- source:
--   General root-connected reduction of all-capital zero-barrier Proposition 1 to boundary valuation, using canonically Proved initial-excess theorem.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0))
    (hval : 0 ≤ barrierValue W 0 0)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by sorry
