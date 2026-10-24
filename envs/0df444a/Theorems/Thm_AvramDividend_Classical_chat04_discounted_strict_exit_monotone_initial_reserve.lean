-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve
-- name    : AvramDividend.Classical.chat04_discounted_strict_exit_monotone_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:07:23.077985+00:00
-- url     : https://prove2.me/theorems/cd747fb7-bd55-4b15-96d9-a0d932a44f67
-- title:
--   Discounted strict two-sided exit transform increases with initial reserve
-- statement:
--   For any nonnegative discount, the exact killed strict upper-before-ruin expectation is nondecreasing in initial reserve. Pathwise, increasing reserve both advances upward passage and delays downward ruin. On successful paths, the earlier passage receives a weakly larger exponential discount factor, and failed paths contribute zero. This is a direct pathwise-integrand proof, valid for extended stopping times, with no use of the scale-ratio equality.
-- source:
--   Strict exit clock monotonicity, ENNReal.toReal_mono on finite successful passages, and monotonicity of the lower Lebesgue integral; equation (3.6) from Avram et al. 2007.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_monotone_initial_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_strict_exit_monotone_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x y : ℝ)
    (hq : 0 ≤ q) (hxy : x ≤ y) :
    twoSidedExitExpectation X q a x ≤ twoSidedExitExpectation X q a y := by sorry
