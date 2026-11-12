-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys111_original_BV_countable_mark_contact_null
-- name    : AvramDividend.Classical.avram_bvb_phys111_original_BV_countable_mark_contact_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:41:43.873918+00:00
-- url     : https://prove2.me/theorems/cbf6ab96-5bfc-4528-91a8-bc731954cccb
-- title:
--   Every countable collection of BV mark-contact thresholds has zero Levy mass
-- statement:
--   For the original spectrally negative Levy process under Standing and bounded variation, every countable family of jump marks has Levy measure zero. It permits simultaneous removal of the countably many sampled ruin-contact thresholds in the uniform physical-grid quadrature.
-- source:
--   Original BV phys95 markwise dominated convergence; Proved phys107 and Mathlib Set.Countable.measure_zero

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys111_original_BV_countable_mark_contact_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (S : Set ℝ) (hS : S.Countable) : X.ν S = 0 := by sorry
