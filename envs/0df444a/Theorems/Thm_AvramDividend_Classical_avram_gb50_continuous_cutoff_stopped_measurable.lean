-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb50_continuous_cutoff_stopped_measurable
-- name    : AvramDividend.Classical.avram_gb50_continuous_cutoff_stopped_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:18:43.325072+00:00
-- url     : https://prove2.me/theorems/e7db129e-bf42-4295-b911-e0ce1611f152
-- title:
--   A continuously clipped coefficient at measurable stopped times is measurable
-- statement:
--   A real coefficient continuous on a measurable interior band can be extended by zero outside the band as a measurable function. Its composition with a measurable reserve, multiplied by a deterministic weight and stopped on a measurable clock event, is measurable. This is the general piecewise-measurable building block of gb47.

import Mathlib
open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_gb50_continuous_cutoff_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Icc a b))
    (Y : Ω → ℝ) (hY : Measurable Y)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (t : ℝ≥0) (k : ℝ) :
    Measurable (fun ω => if t < ρ ω then
      k * (if Y ω ∈ Icc a b then f (Y ω) else 0) else 0) := by
  sorry
