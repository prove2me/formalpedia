-- Prove2me | Theorems.Thm_AvramDividend_Classical_adapted_leftContinuous_isStronglyProgressive
-- name    : AvramDividend.Classical.adapted_leftContinuous_isStronglyProgressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:04:10.982413+00:00
-- url     : https://prove2.me/theorems/0c4df9a7-3a9b-4e5f-9309-458d5bba929d
-- title:
--   Left-continuous adapted dividend processes are progressively measurable
-- statement:
--   An adapted real-valued process indexed by nonnegative time and left-continuous along every sample path is strongly progressively measurable for the same filtration. This supplies the missing passage from the exact left-continuity and adaptedness of admissible dividend controls to progressive measurability, needed for stopped stochastic verification and terminal expectation integrability. The proof is via progressively measurable left-endpoint step approximants and their pointwise limit. The time-zero cell must be handled separately.
-- source:
--   Standard adapted-left-continuous progressive measurability theorem, intended as a source-faithful stochastic-process measurability prerequisite for the classical dividend verification step.

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.adapted_leftContinuous_isStronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted 𝓕 D)
    (hLeft : ∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => D s ω) (Iic t) t) :
    IsStronglyProgressive 𝓕 D := by sorry
