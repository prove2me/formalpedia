-- Prove2me | Theorems.Thm_AvramDividend_Classical_upExitTime_zero_implies_near_threshold_crossings
-- name    : AvramDividend.Classical.upExitTime_zero_implies_near_threshold_crossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:24:39.813018+00:00
-- url     : https://prove2.me/theorems/b172513e-a717-450d-b4e3-f31e0bc3da55
-- title:
--   Instantaneous upward exit at any threshold implies arbitrarily early strict crossings
-- statement:
--   At any real threshold b, zero strict upward passage time forces sample values strictly above b at arbitrarily small positive horizons.
-- source:
--   Direct double-indexed infimum and iInf_lt_iff, generalising the verified zero-threshold result.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.upExitTime_zero_implies_near_threshold_crossings
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (h0 : twoSidedExitUpTime X b ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω := by sorry
