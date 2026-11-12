-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys110_original_BV_finite_activity_ruin_contact_band_mass_vanish
-- name    : AvramDividend.Classical.avram_bvb_phys110_original_BV_finite_activity_ruin_contact_band_mass_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:37:00.702962+00:00
-- url     : https://prove2.me/theorems/57a1bf14-79da-44af-923a-61b14f3027c1
-- title:
--   Original finite-activity BV negative-mark mass vanishes near ruin contact
-- statement:
--   For the exact original spectrally negative Lévy process under Standing, bounded variation, and finite negative-jump activity, the restricted jump mass within a shrinking closed band around the mark that hits a reserve exactly at zero tends to zero.
-- source:
--   Original BV physical-grid compensator quadrature phys95, combining original Standing atomlessness with finite activity and Mathlib interval continuity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys110_original_BV_finite_activity_ruin_contact_band_mass_vanish {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (a : ℝ) : Tendsto (fun δ : ℝ => (X.ν.restrict (Iio (0 : ℝ))) (Icc (-a - δ) (-a + δ))) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by sorry
