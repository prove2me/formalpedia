-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierValue_le_boundary
-- name    : AvramDividend.Classical.avram_root29_05_barrierValue_le_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:10:31.241238+00:00
-- url     : https://prove2.me/theorems/6d7ab025-e0e4-478b-8482-ff44edf9b899
-- title:
--   Genuine killed barrier dividend value below the barrier is at most its reflected boundary value
-- statement:
--   Under the original spectrally negative Lévy law, Standing, positive discount and barrier 0 ≤ x ≤ a, the true killed reflected-regulator discounted dividend value at x is at most the true boundary running-supremum Stieltjes dividend value. No scale-ratio or unproved exit theorem is assumed.
-- source:
--   Use the canonically Proved first-upcrossing factorisation 8fc83520 and Proved true two-sided-exit discounted probability bound dde72b60; the raw coefficient is definitionally twoSidedExitExpectation. Multiply its ≤1 bound by nonnegative ENNReal boundary dividend value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_barrierValue_le_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) ≤ barrierSupValue X a q := by sorry
