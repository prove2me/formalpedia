-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_predictable_section_measurable_public
-- name    : AvramDividend.Classical.avram_chat24_predictable_section_measurable_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:05:27.231386+00:00
-- url     : https://prove2.me/theorems/dcd5a4e1-5e92-42ff-9966-9abd47f5cf6b
-- title:
--   Predictable time sections are measurable
-- statement:
--   Measurable time sections of the predictable sigma algebra; used to pull the actual compact reserve kernel to physical time. Public prerequisite for the public actual-stopped integrability target.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_predictable_section_measurable_public
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable ℝ≥0 (ℝ≥0 × Ω) inferInstance 𝓕.predictable (fun t => (t, ω)) := by sorry
