-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_le_threshold
-- name    : AvramDividend.Classical.firstUpcrossing_value_le_threshold
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:12:51.194052+00:00
-- url     : https://prove2.me/theorems/7d69998c-4968-4ba4-9780-d87464a958a6
-- title:
--   A path with no positive jumps cannot overshoot its first strict upward-passage level
-- statement:
--   For a first strict upward passage time u of a càdlàg path with no positive jumps, all path values at t<u are at most the threshold b. The left limit of the path at any positive u is therefore at most b; because the path has no positive jumps, its value at u is at most that left limit. The u=0 endpoint follows from X_0=0≤b. This is the no-overshoot half of the published firstUpcrossing_value_eq_threshold theorem and reuses the separately Proved prethreshold inequality.
-- source:
--   Avram, Palmowski and Pistorius (2007) first-passage no-overshoot; canonical SpectrallyNegativeLevy.leftLim, noPosJumps and X_zero; pinned Mathlib le_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem firstUpcrossing_value_le_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    X.X u ω ≤ b := by sorry

end AvramDividend.Classical
