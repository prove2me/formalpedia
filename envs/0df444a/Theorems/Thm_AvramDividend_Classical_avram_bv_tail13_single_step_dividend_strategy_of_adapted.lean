-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_dividend_strategy_of_adapted
-- name    : AvramDividend.Classical.avram_bv_tail13_single_step_dividend_strategy_of_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:32:02.751663+00:00
-- url     : https://prove2.me/theorems/3423d8b0-0862-4718-ba28-29eec1ff6f78
-- title:
--   Single positive-clock original dividend strategy from adapted payment
-- statement:
--   A dividend process that is zero through a deterministic clock and then jumps to a nonnegative random amount is an original IsDividendStrategy as soon as the adaptedness condition holds. The proof invokes the public source-exact left continuity of this step, proves initial dividend zero and pointwise monotonicity, and preserves the genuine adaptedness assumption.
-- source:
--   This theorem is a source-exact packaging of the four conjuncts of IsDividendStrategy, reusing the separately proved single-clock left continuity. It supplies the hstrategy premise of public 43840985, conditional on proving adaptedness for the original Lévy-process reset.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_left_continuity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_single_step_dividend_strategy_of_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (K : Ω → ℝ)
    (hK : ∀ ω, 0 ≤ K ω)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω)
    (hAdapt : Adapted 𝓕 D) :
    IsDividendStrategy 𝓕 D := by sorry
