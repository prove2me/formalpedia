-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_adapted
-- name    : AvramDividend.Classical.avram_e0_initial_only_dividend_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:50:54.296044+00:00
-- url     : https://prove2.me/theorems/2e53dd54-2369-406d-a2a1-799bc643517a
-- title:
--   A time-zero measurable dividend mark gives an adapted initial-only strategy
-- statement:
--   A random initial dividend mark measurable at the source filtration's initial sigma-algebra makes the step process with zero value at the origin and constant value later an adapted process. It supplies the original dividend-strategy adaptedness field for an independent geometric reserve mark introduced at time zero.
-- source:
--   Original Avram DividendStrategy, target e0b94d7f, and pinned Filtration.mono/Measurable.mono.

import Mathlib
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_dividend_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (K : Ω → ℝ) (hK : Measurable[𝓕 0] K) :
    Adapted 𝓕 (fun t ω => if t = 0 then 0 else K ω) := by sorry
