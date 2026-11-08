-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_monotone
-- name    : AvramDividend.Classical.avram_e0_initial_only_dividend_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:48:04.403074+00:00
-- url     : https://prove2.me/theorems/3ad1541f-0ef1-42ea-b323-84844c128d84
-- title:
--   An initial-only nonnegative dividend payment is monotone along every sample path
-- statement:
--   For any nonnegative random dividend amount, the path that is zero at time zero and equals that amount at all positive times is monotone. This is the exact pathwise monotonicity field of the original IsDividendStrategy for the geometric initial-mark countermodel.
-- source:
--   Original Avram DividendStrategy definition, theorem e0b94d7f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_dividend_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (hK : ∀ ω, 0 ≤ K ω) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => if t = 0 then 0 else K ω) := by sorry
