-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_band_compensation_identity
-- name    : AvramDividend.Classical.avram_p4_c_generator_cutoff_band_compensation_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:08:57.314633+00:00
-- url     : https://prove2.me/theorems/0b3f7ec1-f903-4e83-ae68-fbf5f103b63e
-- title:
--   On the separated negative-mark compensation band, original generator integrand subtracts the source drift correction
-- statement:
--   On the Lévy annulus -1<z<-ε with ε>0, the source indicator of strict unit jumps equals one. Hence the original integrand is the raw reserve increment minus w'(y)z. This pins down the exact sign and -1 boundary of the source convention without imposing bounded variation.
-- source:
--   Authoritative SpectrallyNegativeLevy.generatorIntegrand definition; Avram–Palmowski–Pistorius generator, Equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_cutoff_band_compensation_identity
    (w : ℝ → ℝ) (y z ε : ℝ)
    (hε : 0 < ε) (hz : z ∈ Ioo (-1 : ℝ) (-ε)) :
    SpectrallyNegativeLevy.generatorIntegrand w y z =
      w (y + z) - w y - deriv w y * z := by sorry
