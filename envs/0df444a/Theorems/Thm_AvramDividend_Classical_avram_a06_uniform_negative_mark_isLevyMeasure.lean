-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_isLevyMeasure
-- name    : AvramDividend.Classical.avram_a06_uniform_negative_mark_isLevyMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:25:13.378763+00:00
-- url     : https://prove2.me/theorems/76b53fa0-d182-47d2-bc4e-051146ca9a77
-- title:
--   The explicit diffuse negative uniform jump measure satisfies the Lévy-measure condition
-- statement:
--   The restriction of Lebesgue measure to the compact negative interval (-1,0) charges no mass to zero and has finite quadratic truncated integral, hence is a genuine Lévy measure. This unlocks the imported pure-jump Lévy-process existence theorem.
-- source:
--   Public Proved 4f8f174b and 51e4a4b3 establish absolute continuity and the quadratic moment; this lemma assembles the IsLevyMeasure predicate.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_negative_mark_isLevyMeasure : ProbabilityTheory.IsLevyMeasure
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) := by sorry
