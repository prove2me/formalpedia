-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_kernel_reflection_ae_measurable_on_left_split
-- name    : AvramDividend.Classical.causal_continuous_kernel_reflection_ae_measurable_on_left_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:05:19.273635+00:00
-- url     : https://prove2.me/theorems/8f98155c-ae98-4632-9d99-296418154e2f
-- title:
--   Positive-time continuous causal kernel remains ae measurable after left-cutoff reflection
-- statement:
--   If κ is continuous on the strictly positive real axis and 0<u<x, then the reflected translate s ↦ κ(x-s) is almost-everywhere strongly measurable on the restricted interval 0<s≤u. Every reflected argument stays strictly positive, so no continuity or boundedness is required at zero. Supplies the Gaussian kernel measurability hypothesis needed by the simultaneous convolution-power induction.
-- source:
--   Compose positive-time continuity with the continuous affine reflection and use pinned ContinuousOn.aestronglyMeasurable on a measurable Ioc interval.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set

theorem AvramDividend.Classical.causal_continuous_kernel_reflection_ae_measurable_on_left_split
    (κ : ℝ → ℝ) (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (x u : ℝ) (hu : 0 < u) (hux : u < x) :
    AEStronglyMeasurable (fun s : ℝ => κ (x - s))
      (volume.restrict (Ioc (0 : ℝ) u)) := by sorry
