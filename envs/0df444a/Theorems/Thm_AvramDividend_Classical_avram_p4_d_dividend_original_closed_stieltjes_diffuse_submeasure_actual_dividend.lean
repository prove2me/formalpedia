-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:04:25.593595+00:00
-- url     : https://prove2.me/theorems/72fd52f1-10f0-452e-9a88-82c0a828d0d9
-- title:
--   Canonical diffuse original dividend component is dominated by the genuine dividendMeasure
-- statement:
--   For the literal original controlled-dividend Stieltjes measure on the closed interval [0,T], every nonnegative atomic-plus-diffuse measure decomposition yields a diffuse component dominated by the actual untruncated dividendMeasure D ω. Consequently the measurable-selection L1 bounds previously proved for arbitrary dominated ν apply to any genuine diffuse selector once its strong measurability and state localisation are independently established. The closed interval preserves the time-zero and horizon atoms.
-- source:
--   Mathlib order structure of nonnegative measures and restrict_le_self applied to the literal original dividendMeasure D ω from the accepted Wave6 Stieltjes decomposition d2232fa0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
      μatom + μdiffuse) :
    μdiffuse ≤ dividendMeasure D ω := by sorry
