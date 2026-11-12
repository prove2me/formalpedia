-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys112_original_BV_positive_occupation_mark_null
-- name    : AvramDividend.Classical.avram_bvb_phys112_original_BV_positive_occupation_mark_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:47:40.301584+00:00
-- url     : https://prove2.me/theorems/149d9e1a-0b19-4772-b270-901cc8fcf85a
-- title:
--   Original BV Levy measure annihilates positive-time occupation levels
-- statement:
--   For the original spectrally negative Levy process, Standing plus bounded variation implies that the Levy measure gives zero mass to all spatial values at which any measurable real path spends positive time. This eliminates possible discontinuity marks for time-integrated physical-grid integrands, including zero-reserve occupation once the path is negated.
-- source:
--   Original BV phys95 positive quadrature; Proved phys111 plus Mathlib Measure.countable_meas_level_set_pos

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys112_original_BV_positive_occupation_mark_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (μ : Measure ℝ≥0) [SFinite μ] (U : ℝ≥0 → ℝ) (hU : Measurable U) : X.ν {z : ℝ | 0 < μ {t : ℝ≥0 | U t = z}} = 0 := by sorry
