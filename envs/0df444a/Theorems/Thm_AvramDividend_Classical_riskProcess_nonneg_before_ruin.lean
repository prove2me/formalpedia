-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
-- name    : AvramDividend.Classical.riskProcess_nonneg_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T09:56:13.688264+00:00
-- url     : https://prove2.me/theorems/c26c83f7-d703-46b9-a361-bf008b70dfe6
-- title:
--   Controlled reserves are nonnegative strictly before the formal ruin time
-- statement:
--   By the definition of ruin time as the infimum of times at which controlled reserves are negative, reserves cannot already be negative at a time strictly before ruin. This pathwise fact is used when applying the verification function w to the stopped controlled reserve in Proposition 4(i).
-- source:
--   Immediate order-theoretic consequence of the canonical ruinTime definition in Def_AvramDividend_Classical_DividendStrategy; supports the stopped-process verification argument for AvramDividend.Classical.admissible_cap_dividendValue_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_nonneg_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by sorry
