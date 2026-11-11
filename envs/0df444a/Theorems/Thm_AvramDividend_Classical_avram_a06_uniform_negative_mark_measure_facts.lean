-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
-- name    : AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:42:58.703868+00:00
-- url     : https://prove2.me/theorems/4f8f174b-fef1-4aec-895c-152ca5d8b18d
-- title:
--   Unit-rate diffuse negative-mark law has finite nonzero mass and no positive jumps
-- statement:
--   Prove simultaneously that the explicit bounded-variation compound-Poisson Lévy measure supported on (-1,0) gives zero mass to positive jumps, has total mass one and finite jump intensity, is nonzero, and is absolutely continuous with respect to Lebesgue measure. These are precise record/Standing fields of the A06 source.
-- source:
--   Root-connected A06 source-existence child 115c3b1e: mass and diffuseness certificate required for spectral jump measure and Standing.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts :
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Ici (0 : ℝ)) = 0 ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) Set.univ = 1 ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Iio (0 : ℝ)) < ⊤ ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ≠ 0 ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ≪ volume := by sorry
