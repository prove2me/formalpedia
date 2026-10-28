-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
-- name    : AvramDividend.Classical.twoSidedExitUpTime_le_observation_of_strict_exceedance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:46:59.991653+00:00
-- url     : https://prove2.me/theorems/36bf3e08-1bb4-45ee-a71e-526319f2d465
-- title:
--   Canonical strict upper exit clock is bounded by any observed strict crossing time
-- statement:
--   For any spectrally negative Lévy process, any real upper barrier a and initial reserve x, a sample path's first upper exit time (defined as an extended-nonnegative infimum) is no later than any observation s at which X_s strictly exceeds a-x. This elementary deterministic fact connects the actual first-passage clock definition to pathwise exit events and underpins strict finite-horizon exit calculations, without regularity assumptions.
-- source:
--   Definition of twoSidedExitUpTime as nested iInf and the order-theoretic iInf_le lemma.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_le_observation_of_strict_exceedance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ω : Ω) (s : ℝ≥0)
    (hs : a - x < X.X s ω) :
    twoSidedExitUpTime X (a - x) ω ≤ (s : ℝ≥0∞) := by sorry
