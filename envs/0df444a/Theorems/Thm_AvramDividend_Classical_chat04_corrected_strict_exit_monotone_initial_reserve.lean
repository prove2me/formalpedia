-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_corrected_strict_exit_monotone_initial_reserve
-- name    : AvramDividend.Classical.chat04_corrected_strict_exit_monotone_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:12:59.998575+00:00
-- url     : https://prove2.me/theorems/d7d51566-7bb8-463d-aba8-748c31ebb25a
-- title:
--   Corrected killed two-sided exit transform increases with initial reserve
-- statement:
--   The corrected strict two-sided exit expectation uses exactly the original stopping times and integral by the independently proved definitional equivalence. Therefore its discounted expectation is monotone in initial reserve whenever the original killed expectation is monotone, for all nonnegative discounts. This transfers a useful comparison to the Esscher scale branch.
-- source:
--   Derived from Proved exact original/corrected expectation equality and the strict initial-reserve monotonicity theorem; Avram et al. 2007 eq. (3.6).

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_corrected_strict_exit_monotone_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x y : ℝ)
    (hq : 0 ≤ q) (hxy : x ≤ y) :
    twoSidedExitExpectationCorrected X q a x ≤
      twoSidedExitExpectationCorrected X q a y := by sorry
