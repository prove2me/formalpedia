-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
-- name    : AvramDividend.Classical.avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:13:54.281029+00:00
-- url     : https://prove2.me/theorems/ced10a95-56a4-47c7-9a07-2ba154e8d8df
-- title:
--   Deterministic horizon support is predictable in the actual right-continuous time-probability mark space
-- statement:
--   Every deterministic finite horizon event t≤T, viewed on actual right-continuous predictable time-probability × Borel mark space, is measurable. Thus the horizon-support indicator needed in original-source stopped predictable compensation is automatically predictable; no extra hS hypothesis is mathematically needed when S is this literal horizon set.
-- source:
--   Mathlib measurableSet_predictable_Ioi_prod for the deterministic future interval times Ω; take its complement and form a product with all marks.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} := by sorry
