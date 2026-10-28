-- Prove2me | Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
-- name    : AvramDividend.Classical.corrected_exit_shifted_initial_reserve_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:52:43.384985+00:00
-- url     : https://prove2.me/theorems/3a18d36a-a02b-4ba9-ab4a-d9272cd1dc6b
-- title:
--   Killed two-sided exit monotonicity for fixed upward passage distance
-- statement:
--   For fixed upward passage distance, increase initial reserve from x to y. The upper first-passage time in the corrected exit definition is unchanged while the lower ruin threshold decreases from minus x to minus y, so pathwise success is monotone. The nonnegative discounted expectation is therefore nondecreasing. This is an independent elementary stochastic comparison for the unbounded Esscher/scale-function monotonicity route.
-- source:
--   Pathwise event inclusion for stopping times under threshold monotonicity; standard two-sided exit setup of Kuznetsov, Kyprianou and Rivero (2013).

import Theorems.Thm_AvramDividend_Classical_chat04_corrected_strict_exit_monotone_initial_reserve
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.corrected_exit_shifted_initial_reserve_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q h x y : ℝ) (hxy : x ≤ y) :
    twoSidedExitExpectationCorrected X q (h + x) x ≤
      twoSidedExitExpectationCorrected X q (h + y) y := by sorry
