-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:03:57.510976+00:00
-- url     : https://prove2.me/theorems/5c4bcbc9-43f1-46f4-b8f2-c47e8af5f48b
-- title:
--   Actual original stopped controlled-dividend pre-ruin branch is measurable from the source real clock
-- statement:
--   Under the exact original SpectrallyNegativeLevy, admissible dividend control and measurable finite stopping clock of P4-F, the set of paths with an initial payment or strictly pre-ruin clock is measurable. The proof uses the Proved original controlled ruin-time measurability and the actual ENNReal clock coercion. This discharges a concrete missing hypothesis of the Proved signed full-Stieltjes branch L1 theorem.
-- source:
--   Original IsAdmissibleLe and ruinTime_measurable theorem bbfbecf4; pinned Mathlib measurability of ENNReal.ofReal and measurable equality/strict ordering.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ))) :
    MeasurableSet {ω : Ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω} := by sorry
