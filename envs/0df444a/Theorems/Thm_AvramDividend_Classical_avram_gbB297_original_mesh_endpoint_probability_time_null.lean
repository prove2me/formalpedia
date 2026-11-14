-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB297_original_mesh_endpoint_probability_time_null
-- name    : AvramDividend.Classical.avram_gbB297_original_mesh_endpoint_probability_time_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:19:34.568863+00:00
-- url     : https://prove2.me/theorems/52015c80-c944-4699-8427-84c08acb7eab
-- title:
--   Finite physical mesh endpoints have zero original product probability-time measure
-- statement:
--   For any original sample measure, the probability-by-physical-time product mass of pairs whose time belongs to a finite grid endpoint set is zero. Each outcome section is exactly the finite time set, which has zero volume by the Proved B283, and Tonelli integrates zero. Supplies the authentic null-boundary input for combining B292, B290 and B296 into B276b.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB297_original_mesh_endpoint_probability_time_null
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ) (δ : ℝ) :
    (P.prod volume)
      {z : Ω × ℝ |
        z.2 ∈ Set.range (fun i : Fin N => (i : ℝ) * δ)} = 0 := by sorry
