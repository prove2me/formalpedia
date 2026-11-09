-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_source14_original_dividend_rightLimit_leftLim_eq_pre
-- name    : AvramDividend.Classical.avram_bv_source14_original_dividend_rightLimit_leftLim_eq_pre
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:29:13.3812+00:00
-- url     : https://prove2.me/theorems/b1c68bbe-be4b-471c-85e1-fb32d09f0e51
-- title:
--   Original admissible left-continuous dividend has left limit of right-payment value equal to prepayment value
-- statement:
--   For the actual dividend strategy D, monotonicity and left continuity imply that the left limit, at each strictly positive time, of the right-payment process rightLimit D equals the original prepayment D(t). The proof squeezes rightLimit D(s) between D(s) and D(t) as s approaches t from below. This is the missing exact source interface between the predictable stopped zero-prestate mask and the negative-jump ruin contact, needed for the stopped BV HJB reward budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_source14_original_dividend_rightLimit_leftLim_eq_pre
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) t = D t ω := by sorry
