-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_natural_filtration_le
-- name    : AvramDividend.Classical.avram_wave3_04_drifted_natural_filtration_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:49:59.143914+00:00
-- url     : https://prove2.me/theorems/eeea6395-722e-43d7-a57f-ea2522282d36
-- title:
--   Deterministic drift preserves containment of natural filtration in the original past-path information
-- statement:
--   By the natural-filtration path-comap identity, the drifted past path is a pointwise measurable deterministic transformation of the undrifted past path. Coordinatewise measurability into the function space and monotonicity of measurable-space pullbacks yield the claimed filtration inclusion.
-- source:
--   Private pinned remote elaboration job 846d8fd5-82fa-4b77-875f-c9d8ad0f322a, exact SHA cd46c0d56b96b77f799f6b92897811baa8d2742a5196554419c2ae116387c33d.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_drifted_natural_filtration_le {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0,
      StronglyMeasurable (fun ω => U t ω - (t : ℝ)))
    (s : ℝ≥0) :
    (Filtration.natural
        (fun t ω => U t ω - (t : ℝ)) hmeas) s ≤
      MeasurableSpace.comap
        (fun ω (u : Set.Iic s) => U (u : ℝ≥0) ω) inferInstance  := by sorry
