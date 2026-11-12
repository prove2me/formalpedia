-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva45_original_countable_grid_shifted_mark_contacts_null
-- name    : AvramDividend.Classical.avram_bva45_original_countable_grid_shifted_mark_contacts_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:57:34.143095+00:00
-- url     : https://prove2.me/theorems/270a5821-dfc1-4af8-88f4-ab96ec1237e0
-- title:
--   All countably many physical grid reserve contact thresholds have zero negative jump intensity
-- statement:
--   For a countable family of original physical-grid reserve values, the entire set of negative jump marks hitting a fixed boundary is null under the Standing BV Levy measure. This simultaneously excludes all grid-dependent jump-mark contact discontinuities and is needed to take almost-everywhere limits across all mesh refinements in the source compensator quadrature.
-- source:
--   Original one-sided compensator quadrature e5edbe9b-78cf-4121-bb35-2f016cf0e2cb and positive finite mark physical source 4287fafd-afdc-46b2-a160-033b7b2500f2, authored 11 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bva45_original_countable_grid_shifted_mark_contacts_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ) (hStanding : X.Standing) (hBV : X.BoundedVariation) (a : ℕ → ℝ) (b : ℝ) : X.ν {z : ℝ | ∃ n : ℕ, a n + z = b} = 0 := by sorry
