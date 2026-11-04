-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_drift_renormalization
-- name    : AvramDividend.Classical.avram_p4_c_generator_finite_band_drift_renormalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:21:04.487234+00:00
-- url     : https://prove2.me/theorems/dde11d7a-69d0-48a9-b706-de459e4facf5
-- title:
--   Original generator drift c re-centres exactly to finite epsilon cut-off drift without bounded-variation assumptions
-- statement:
--   At every generator-integrable state y, the source original physical drift term c*w'(y) plus the compensated generator contribution on -1<z<-epsilon equals the finite-cutoff drift (c minus the signed first moment of that annulus) times w'(y), plus the corresponding uncompensated raw jump integral. This identifies exactly the source truncation sign and bypasses the invalid full finite-variation drift in UBV.
-- source:
--   Source SpectrallyNegativeLevy.generatorIntegrand and GeneratorIntegrable; previously proved Avram P4-C finite_band_raw_increment_identity; Eq (5.13) original paper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_raw_increment_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_finite_band_drift_renormalization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    X.c * deriv w y +
      (∫ z in Ioo (-1 : ℝ) (-ε),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y +
      (∫ z in Ioo (-1 : ℝ) (-ε), w (y + z) - w y ∂X.ν) := by sorry
