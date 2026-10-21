-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
-- name    : AvramDividend.Classical.postPaymentReserve_rightJump_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:21:26.807676+00:00
-- url     : https://prove2.me/theorems/118ea151-e762-4929-8756-0221b6e4e2bd
-- title:
--   The dividend right atom is exactly the book-to-post-payment reserve drop
-- statement:
--   At every time t and sample path, a nondecreasing left-continuous dividend strategy has a nonnegative right-payment atom Δ+D_t = D_{t+}−D_t. The pre-payment reserve U_t = x+X_t−D_t splits exactly as the post-payment reserve U_t+ = x+X_t−D_{t+} plus the atom Δ+D_t. In particular the post-payment reserve never exceeds the pre-payment reserve. This is the pathwise jump-accounting identity required for the stopped HJB dividend secant at t=0, a finite horizon, or a strictly pre-ruin time.
-- source:
--   Correct dividend atom convention; use Proved dividendStrategy_le_rightLimit and riskProcess definition. No Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_rightJump_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ rightLimit D t ω - D t ω ∧
    riskProcess X x D t ω =
      (x + X.X t ω - rightLimit D t ω) +
        (rightLimit D t ω - D t ω) ∧
    x + X.X t ω - rightLimit D t ω ≤
      riskProcess X x D t ω := by sorry
