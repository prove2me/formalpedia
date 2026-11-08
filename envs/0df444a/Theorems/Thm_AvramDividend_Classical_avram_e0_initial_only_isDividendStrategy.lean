-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_isDividendStrategy
-- name    : AvramDividend.Classical.avram_e0_initial_only_isDividendStrategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:09:36.35355+00:00
-- url     : https://prove2.me/theorems/ead94903-757f-4d85-b07d-10dd0a56d489
-- title:
--   An initially measurable nonnegative single payment is an original dividend strategy
-- statement:
--   A nonnegative dividend mark measurable at time zero defines a cumulative dividend strategy which vanishes at clock zero and equals that mark at all later clocks. Pathwise monotonicity, source-exact left continuity, and filtration adaptedness are supplied by the three already Proved named theorems.
-- source:
--   Original IsDividendStrategy and Proved theorem IDs 3ad1541f, 2e53dd54, 749f8dc1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_monotone
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_adapted
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_leftcont
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_isDividendStrategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKmeas : Measurable[𝓕 0] K) :
    IsDividendStrategy 𝓕 (fun t ω => if t = 0 then 0 else K ω) := by sorry
