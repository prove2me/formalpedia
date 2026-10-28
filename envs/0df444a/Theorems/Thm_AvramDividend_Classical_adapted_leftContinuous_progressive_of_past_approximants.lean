-- Prove2me | Theorems.Thm_AvramDividend_Classical_adapted_leftContinuous_progressive_of_past_approximants
-- name    : AvramDividend.Classical.adapted_leftContinuous_progressive_of_past_approximants
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:03:08.235257+00:00
-- url     : https://prove2.me/theorems/cc14ef21-864f-4d9c-9311-a8518db0dd90
-- title:
--   Adapted left-continuous processes are progressive given finite-valued past-time approximants
-- statement:
--   For a strongly adapted process with left-continuous sample paths, assume measurable, locally finite-valued past-time samplers converge to each time from the left. Then the process is strongly progressive. This reduces the full adapted-left-continuity progressive-measurability theorem to construction of the samplers, while retaining time-zero and past-adaptedness requirements. It combines already Proved finite-range progressive sampling and pointwise-limit closure.
-- source:
--   Standard approximation proof for adapted left-continuous processes, using Proved AvramDividend.Classical.stronglyProgressive_of_past_finiteRange_sample and progressive_of_pointwise_progressive_approximants.

import Mathlib.Probability.Process.Adapted
import Theorems.Thm_AvramDividend_Classical_stronglyProgressive_of_past_finiteRange_sample
import Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.adapted_leftContinuous_progressive_of_past_approximants
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted 𝓕 D)
    (hLeft : ∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => D s ω) (Iic t) t)
    (g : ℕ → ℝ≥0 → ℝ≥0)
    (hg_meas : ∀ n, Measurable (g n))
    (hg_past : ∀ n t, g n t ≤ t)
    (hg_finite : ∀ n T, (g n '' Iic T).Finite)
    (hg_tendsto : ∀ t, Filter.Tendsto (fun n => g n t) Filter.atTop
      (nhdsWithin t (Iic t))) :
    IsStronglyProgressive 𝓕 D := by sorry
