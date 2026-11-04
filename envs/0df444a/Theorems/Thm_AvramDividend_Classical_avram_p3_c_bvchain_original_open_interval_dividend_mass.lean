-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_open_interval_dividend_mass
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_open_interval_dividend_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:47:09.382019+00:00
-- url     : https://prove2.me/theorems/6d262fb9-9cc7-464a-afc4-7598df31ab58
-- title:
--   Original left-continuous dividend strict-open Stieltjes mass with both endpoint atoms excluded
-- statement:
--   The original left-continuous dividend strategy has Stieltjes mass on the strictly open interval (a,b) exactly equal to D b before its right payment minus rightLimit D a after its right payment, excluding both endpoint atoms.
-- source:
--   Original DividendStrategy; Mathlib StieltjesFunction.measure_Ioo, dividendStrategy_real_extension_leftContinuous and dividendPath_real_rightLim_eq_rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_open_interval_dividend_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) :
    dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - rightLimit D a ω) := by sorry
