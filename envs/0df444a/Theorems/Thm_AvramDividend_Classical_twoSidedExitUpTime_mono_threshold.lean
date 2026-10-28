-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
-- name    : AvramDividend.Classical.twoSidedExitUpTime_mono_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:21:03.859694+00:00
-- url     : https://prove2.me/theorems/5060f2c9-5c3e-48d5-a44c-101f9a63f35a
-- title:
--   Strict upper exit time is monotone in the crossing threshold
-- statement:
--   For each Lévy path, if a ≤ b, the first strict crossing above a occurs no later than the first strict crossing above b. This supports monotone approximation of exit boundaries and bounded-horizon passage arguments.
-- source:
--   Nested indexed-infimum definition of twoSidedExitUpTime and order bounds for strict inequalities.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_mono_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    twoSidedExitUpTime X a ω ≤ twoSidedExitUpTime X b ω := by sorry
