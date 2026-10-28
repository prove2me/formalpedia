-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_antitone_threshold
-- name    : AvramDividend.Classical.twoSidedExitDownTime_antitone_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:20:21.755743+00:00
-- url     : https://prove2.me/theorems/c1d47f19-2ec2-4a6a-9749-05f3d39351d7
-- title:
--   Strict lower exit time is antitone in the crossing threshold
-- statement:
--   For fixed Lévy path, a ≤ b implies that the first strict crossing below b occurs no later than the first strict crossing below a. This monotonicity is useful for two-sided exit comparisons and threshold approximation without extra sample-path hypotheses.
-- source:
--   Nested infimum definition of the canonical twoSidedExitDownTime and order monotonicity of indexed infima.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_antitone_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    twoSidedExitDownTime X b ω ≤ twoSidedExitDownTime X a ω := by sorry
