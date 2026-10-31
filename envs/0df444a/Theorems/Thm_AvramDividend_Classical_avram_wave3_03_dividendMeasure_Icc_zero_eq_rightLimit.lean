-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
-- name    : AvramDividend.Classical.avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:27:43.403414+00:00
-- url     : https://prove2.me/theorems/d6ace15b-26cc-4400-be9b-8c4d19980128
-- title:
--   Closed-horizon actual dividend Stieltjes mass includes the terminal right jump
-- statement:
--   For every adapted monotone left-continuous admissible cumulative dividend path D, its actual Stieltjes dividendMeasure assigns to [0,T] precisely ENNReal.ofReal(rightLimit D T ω). This includes every continuous, singular-continuous, initial-time and terminal-time right-jump payment without any purely atomic concentration assumption. It upgrades the already Proved [0,T) cumulative identity by the exact terminal singleton atom.
-- source:
--   Combine accepted dividendMeasure_Ico_zero_eq_dividendValue (56472398), accepted singleton right jump (4f229f9a), monotonicity and the definition rightLimit; use measure_union on [0,T) and {T}.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    dividendMeasure D ω (Icc (0 : ℝ) (T : ℝ)) =
      ENNReal.ofReal (rightLimit D T ω) := by sorry
