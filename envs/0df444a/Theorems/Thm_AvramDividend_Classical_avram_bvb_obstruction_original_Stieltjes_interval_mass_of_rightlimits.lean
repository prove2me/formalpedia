-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_Stieltjes_interval_mass_of_rightlimits
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_Stieltjes_interval_mass_of_rightlimits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:41:07.143828+00:00
-- url     : https://prove2.me/theorems/f1faef61-6967-48bc-99aa-c3fe5760196c
-- title:
--   Original dividend Stieltjes interval mass from exact endpoint right limits of the actual dividend path
-- statement:
--   For any original dividend strategy whose induced real-time dividend function has right limit zero at time zero and right limit t at time t, the original dividend Stieltjes measure of (0,t] is precisely t. The explicit right-limit hypotheses accommodate genuine right-payment jumps and avoid the false unrestricted claim that D(s)=s on [0,t] alone rules out a jump immediately after t.
-- source:
--   Unfold the actual dividendMeasure definition and the source StieltjesFunction.measure_Ioc theorem. Pinned Monotone.stieltjesFunction_eq converts the Stieltjes endpoint values to the right limits of the original dividend function; use the explicit two endpoint hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_Stieltjes_interval_mass_of_rightlimits
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (hRight0 : Function.rightLim
      (fun z : ℝ => D z.toNNReal ω) 0 = 0)
    (hRightt : Function.rightLim
      (fun z : ℝ => D z.toNNReal ω) (t : ℝ) = (t : ℝ)) :
    dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (t : ℝ) := by sorry
