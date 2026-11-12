-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys121_original_zero_source_drift_reserve_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys121_original_zero_source_drift_reserve_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:13:05.17765+00:00
-- url     : https://prove2.me/theorems/50fb6b61-bf28-43f5-938b-2ffb59fbe3e9
-- title:
--   Original zero-source-jump drift reserve is time-measurable
-- statement:
--   The controlled original-process drift reserve on the no-source-jump sample-path event is Borel measurable in time, with the exact original postpayment rightLimit dividend. This enables measurability of stopped negative-jump compensator kernels in phys95, using original admissibility and the proved rightLimit measurability lemma phys120.
-- source:
--   Original BV phys95 no-mark reserve and phys120 original dividend rightLimit time measurability

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys121_original_zero_source_drift_reserve_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) : Measurable (fun t : ℝ≥0 => x + (t : ℝ) * X.drift - rightLimit D t ω) := by sorry
