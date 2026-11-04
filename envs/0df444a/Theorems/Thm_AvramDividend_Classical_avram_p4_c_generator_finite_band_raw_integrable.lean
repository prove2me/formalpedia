-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_raw_integrable
-- name    : AvramDividend.Classical.avram_p4_c_generator_finite_band_raw_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:44:06.149971+00:00
-- url     : https://prove2.me/theorems/7dfc2973-0325-404a-9729-62b1ef8cd0d4
-- title:
--   Original generator-integrable payoff gives absolutely integrable actual jump increments on the separated finite compensation band
-- statement:
--   For any original spectrally negative Lévy generator-integrable payoff, ε>0 makes the finite mark annulus -1<z<-ε have integrable raw jumps w(y+z)-w(y). This follows from source GeneratorIntegrable for K, ν-integrability of z over the separated annulus, and the exact source compensation identity. It establishes L1 control of the raw large-jump integrand for compensation without assuming UBV first moments near zero.
-- source:
--   Proved original finite band cutoff linear mark integral 63c53f4c-113e-48e0-8d54-55be014f9398 and source compensation identity 0b3f7ec1-f903-4e83-ae68-fbf5f103b63e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_band_compensation_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_finite_band_raw_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Ioo (-1 : ℝ) (-ε)) X.ν := by sorry
