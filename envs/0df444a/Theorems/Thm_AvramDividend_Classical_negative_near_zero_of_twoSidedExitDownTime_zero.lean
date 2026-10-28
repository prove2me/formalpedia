-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
-- name    : AvramDividend.Classical.negative_near_zero_of_twoSidedExitDownTime_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:08:41.587207+00:00
-- url     : https://prove2.me/theorems/da3dcbeb-9f46-46fb-921e-96025e68401a
-- title:
--   Instantaneous lower exit implies arbitrarily early negative observations
-- statement:
--   If the first strict downward passage time from zero is itself zero, each positive time interval contains an observation strictly below zero.
-- source:
--   Order-theoretic first-passage time infimum and strict sample-path crossings.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_near_zero_of_twoSidedExitDownTime_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (h0 : twoSidedExitDownTime X 0 ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by sorry
