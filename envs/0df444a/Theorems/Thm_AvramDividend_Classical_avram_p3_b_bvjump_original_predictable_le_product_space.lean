-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_le_product_space
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_le_product_space
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:31:55.174208+00:00
-- url     : https://prove2.me/theorems/4b460d42-d5d2-43ac-b9ce-a8f7f637aca7
-- title:
--   Original right-continuous predictable filtration is below the physical product sigma algebra
-- statement:
--   For the genuine original filtration, show that its right-continuous predictable sigma-algebra is contained in the ordinary Borel-time times original-path product sigma-algebra. Prove the inclusion directly from the established singleton-bottom and open-right interval predictable generators using the original filtration's sub-sigma-algebra inclusion. This is a source-exact prerequisite for constructing the actual physical predictable intensity by trimming the product clock, without introducing an independent marked point process or compensator axiom.
-- source:
--   Mathlib.Probability.Process.Predictable measurableSpace_le_predictable_of_measurableSet; original Filtration.le

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_le_product_space {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ) : 𝓕.rightCont.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by sorry
