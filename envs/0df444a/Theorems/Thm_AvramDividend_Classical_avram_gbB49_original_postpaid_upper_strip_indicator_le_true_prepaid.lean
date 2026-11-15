-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
-- name    : AvramDividend.Classical.avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:12:01.757863+00:00
-- url     : https://prove2.me/theorems/5cf6517e-81d3-4ba6-a150-62149eb655ba
-- title:
--   Original controlled Gaussian postpayment upper-strip occupation indicator is bounded by the true prepayment indicator
-- statement:
--   For every physical time and original admissible dividend strategy, rightLimit D(t)≥D(t) implies the postpayment reserve x+X(t)-rightLimit D(t) is at most the original prepayment riskProcess. Its upper clipping-strip indicator is therefore bounded by the true prepayment upper-strip indicator used in the finite-cap stopped cash occupation charge. This provides the missing pre/post occupation bridge in the Gaussian B21 proof.
-- source:
--   The proved dividendStrategy_le_rightLimit establishes D(t)≤rightLimit D(t). Comparing original postpayment and prepayment reserves immediately gives upper-strip event inclusion and indicator monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    (if b < x + X.X t ω - rightLimit D t ω
      then (1 : ℝ) else 0) ≤
    (if b < riskProcess X x D t ω
      then (1 : ℝ) else 0) := by sorry
