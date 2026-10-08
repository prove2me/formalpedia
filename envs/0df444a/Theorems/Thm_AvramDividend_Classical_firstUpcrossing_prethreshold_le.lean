-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
-- name    : AvramDividend.Classical.firstUpcrossing_prethreshold_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:55:23.247689+00:00
-- url     : https://prove2.me/theorems/ca03b30a-8ef0-4424-b880-caf139df13fe
-- title:
--   Before a first strict upward passage the Lévy path stays below its threshold
-- statement:
--   The first strict upward passage is defined as an infimum of the times at which a sample path strictly exceeds a real threshold b. If a time t were strictly before the first passage but X_t>b, t itself would belong to the set over which the infimum is taken, implying that the infimum is no greater than t, a contradiction. The result is purely order-theoretic, does not require no-positive-jumps or stopping-time properties, and is an important prerequisite to proving that an eventual upward crossing is an attained running-supremum peak.
-- source:
--   Canonical strict first-upcrossing time defined as a dependent infimum in Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity; order structure of ENNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem firstUpcrossing_prethreshold_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0, t < u → X.X t ω ≤ b := by sorry
end AvramDividend.Classical
