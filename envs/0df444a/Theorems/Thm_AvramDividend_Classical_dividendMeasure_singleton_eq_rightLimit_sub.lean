-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
-- name    : AvramDividend.Classical.dividendMeasure_singleton_eq_rightLimit_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:07:11.64551+00:00
-- url     : https://prove2.me/theorems/4f229f9a-6d10-43ea-aea7-c2db48b444ec
-- title:
--   Dividend measure singleton atom equals the admissible strategy's rightLimit payment
-- statement:
--   For every actual dividend strategy D, sample path ω and nonnegative time t, the Stieltjes measure dividendMeasure D ω assigns exactly ENNReal.ofReal(rightLimit D t ω−D t ω) to the singleton {t}. This is the precise mission-defined dividend jump, and joins the independently established path-continuity, Stieltjes atom and right-limit identification theorems. It is needed to connect the jump-payment inequality to the atomic part of dividendValue.
-- source:
--   Children dividendMeasure_singleton_rightJump_extended and dividendPath_real_rightLim_eq_rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_singleton_eq_rightLimit_sub
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    dividendMeasure D ω {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω) := by sorry
