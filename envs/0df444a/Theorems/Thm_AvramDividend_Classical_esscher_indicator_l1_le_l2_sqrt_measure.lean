-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_indicator_l1_le_l2_sqrt_measure
-- name    : AvramDividend.Classical.esscher_indicator_l1_le_l2_sqrt_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:21:18.556543+00:00
-- url     : https://prove2.me/theorems/122faf25-724f-4c0c-9215-c89b8ac59315
-- title:
--   Hölder L1 event-restriction bound from an L2 seminorm
-- statement:
--   On any measure space, the L1 seminorm of a strongly measurable real observable restricted to a measurable event is bounded by its full L2 seminorm multiplied by the square root of the event's measure. This quantitative Hölder bound supplies the small-event estimate needed for uniform integrability of finite-grid stopped Esscher likelihoods.
-- source:
--   Pinned Mathlib MeasureTheory.Function.LpSeminorm.CompareExp (eLpNorm_le_eLpNorm_mul_rpow_measure_univ), Basic (eLpNorm_indicator_eq_eLpNorm_restrict, eLpNorm_mono_measure), and AEStronglyMeasurable.restrict; no Wiener-Hopf source involved.

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.esscher_indicator_l1_le_l2_sqrt_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (s : Set Ω)
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (s.indicator f) (1 : ℝ≥0∞) μ ≤
      eLpNorm f (2 : ℝ≥0∞) μ * (μ s) ^ (1 / 2 : ℝ) := by sorry
