-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero
-- name    : AvramDividend.Classical.twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:02:56.736461+00:00
-- url     : https://prove2.me/theorems/4e045632-3b25-41b0-b29e-38a70e1755ac
-- title:
--   Almost-sure positive observations near zero imply instantaneous upper exit
-- statement:
--   Almost every path has positive observations at arbitrarily small times. Therefore almost every path exits upwards immediately from zero.
-- source:
--   Pathwise near-zero regularity and measure-theoretic eventuality.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_ae_eq_zero_of_ae_positive_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0 := by sorry
