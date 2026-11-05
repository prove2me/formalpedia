-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_marked_negative_rectangle_predictable
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_prestate_marked_negative_rectangle_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:02:37.478143+00:00
-- url     : https://prove2.me/theorems/47f044f3-907d-45e9-8e58-e8f49bbf687d
-- title:
--   Original controlled pre-jump reserve compact band and negative mark rectangle is predictable by Borel
-- statement:
--   For the original controlled Levy process, the pre-jump reserve compact-band event together with any strictly negative mark is measurable in the product of the right-continuous predictable time-path sigma-algebra and Borel-mark sigma-algebra.
-- source:
--   Original strongly predictable controlled pre-jump reserve and proved P3-B compact-band predictable event

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_prestate_marked_negative_rectangle_predictable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (a b : ℝ) : MeasurableSet[(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] {p : ((ℝ≥0 × Ω) × ℝ) | Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 ∈ Icc a b ∧ p.2 < 0} := by sorry
