-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_near_zero_of_twoSidedExitUpTime_zero
-- name    : AvramDividend.Classical.positive_near_zero_of_twoSidedExitUpTime_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:08:43.394296+00:00
-- url     : https://prove2.me/theorems/019f6e5a-7572-4456-a927-4036b252b6af
-- title:
--   Instantaneous upper exit implies arbitrarily early positive observations
-- statement:
--   If the first strict upward passage time from zero is itself zero, each positive time interval contains an observation strictly above zero.
-- source:
--   Order-theoretic first-passage time infimum and strict sample-path crossings.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_near_zero_of_twoSidedExitUpTime_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (h0 : twoSidedExitUpTime X 0 ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by sorry
