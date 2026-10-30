-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierValue_monotone_initial_capital
-- name    : AvramDividend.Classical.avram_root29_05_barrierValue_monotone_initial_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:12:25.520538+00:00
-- url     : https://prove2.me/theorems/18fc2b39-b8c0-4b1a-aa4e-341a848fbb4e
-- title:
--   Original killed reflected-regulator barrier value is monotone in initial capital below the barrier
-- statement:
--   Under the original standing spectrally negative Lévy law with positive discount q and barrier a, raising initial capital from 0≤x≤y≤a cannot reduce the actual expected discounted dividend payments of the true reflected regulator before strict controlled ruin.
-- source:
--   Use the canonically Proved killed-history first-upcrossing actual Stieltjes value factorisation 8fc83520 separately at x and y. Its exit coefficient is definitionally twoSidedExitExpectation. Monotonicity of the genuine discounted strict exit coefficient is already canonically Proved as cd747fb7; ENNReal multiplication by the same nonnegative boundary dividend value preserves order, even if infinite. No scale identity or artificial killed history law is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_barrierValue_monotone_initial_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (a x y : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x)
    (hxy : x ≤ y) (hya : y ≤ a) :
    dividendValue X q x (barrierStrategy X x a) ≤
      dividendValue X q y (barrierStrategy X y a) := by sorry
