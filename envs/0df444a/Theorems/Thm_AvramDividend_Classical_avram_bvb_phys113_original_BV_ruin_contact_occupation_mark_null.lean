-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys113_original_BV_ruin_contact_occupation_mark_null
-- name    : AvramDividend.Classical.avram_bvb_phys113_original_BV_ruin_contact_occupation_mark_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:50:45.88863+00:00
-- url     : https://prove2.me/theorems/a082bdfb-b834-4680-9f92-6e699bb94518
-- title:
--   Original BV ruin-contact marks with positive-time occupation have zero Levy mass
-- statement:
--   For the original Standing bounded-variation Levy process and any measurable reserve path U, the jump marks z for which the reserve equals -z for positive time carry zero Levy mass. This is the precise jump-to-zero discontinuity exclusion needed to take one-sided marked integrand limits in the original physical-grid quadrature phys95.
-- source:
--   Original BV phys95 zero-contact mark quadrature, Proved phys111 and Mathlib countable_meas_level_set_pos

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys113_original_BV_ruin_contact_occupation_mark_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (μ : Measure ℝ≥0) [SFinite μ] (U : ℝ≥0 → ℝ) (hU : Measurable U) : X.ν {z : ℝ | 0 < μ {t : ℝ≥0 | U t = -z}} = 0 := by sorry
