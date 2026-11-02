-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_original_predictable
-- name    : AvramDividend.Classical.avram_wave5_02c_deterministic_horizon_mask_original_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:23:24.609492+00:00
-- url     : https://prove2.me/theorems/ebd42ab1-1310-497b-b2a2-ce5696efdfbf
-- title:
--   Deterministic stopped horizon mask is predictable in the unchanged original filtration
-- statement:
--   For any filtration of the original source, without passing to its right-continuous modification, the deterministic support t≤T is measurable in its own predictable time-probability × Borel mark sigma-algebra. This eliminates the artificial hS horizon-mask hypothesis from the original intrinsic stopped compensation theorem while retaining genuine source-kernel and rectangle assumptions.
-- source:
--   Pinned Mathlib predictable Ioi future-cylinder generator with 𝓕 itself, complement and mark-space product.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_02c_deterministic_horizon_mask_original_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} := by sorry
