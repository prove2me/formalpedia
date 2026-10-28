-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_surviving_riskProcess_range_real_finite
-- name    : AvramDividend.Classical.capped_surviving_riskProcess_range_real_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:59:46.25425+00:00
-- url     : https://prove2.me/theorems/78d2f686-58ea-46a7-be90-a04f6d2fe5d7
-- title:
--   The controlled reserve is in its finite real cap before ruin
-- statement:
--   At every finite time strictly before ruin, an admissible capped controlled reserve lies in the closed real interval from zero to B. This applies the canonically proved pre-ruin extended-real cap theorem and converts the ENNReal inequality to real order.
-- source:
--   Avram capped_riskProcess_range_before_ruin_including_zero and pinned Mathlib ENNReal.ofReal_le_ofReal_iff.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_surviving_riskProcess_range_real_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x B : ℝ) (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (ω : Ω) (t : ℝ≥0)
    (hBefore : (t : ℝ≥0∞) < ruinTime X x D ω) :
    riskProcess X x D t ω ∈ Icc (0 : ℝ) B := by sorry
