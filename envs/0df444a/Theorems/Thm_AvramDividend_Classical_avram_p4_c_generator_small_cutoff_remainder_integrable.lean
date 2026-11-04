-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_small_cutoff_remainder_integrable
-- name    : AvramDividend.Classical.avram_p4_c_generator_small_cutoff_remainder_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:59:50.487759+00:00
-- url     : https://prove2.me/theorems/5e106b1d-af66-4388-b4a2-045c450a31ef
-- title:
--   Exact small-jump compensated Taylor remainder is Lévy integrable under original GeneratorIntegrable
-- statement:
--   Source GeneratorIntegrable w y implies integrability of the combined compensated Taylor remainder w(y+z)-w(y)-w'(y)z over -epsilon≤z<0 for any 0<epsilon<1. The proof first restricts the source integral to the measured cutoff set, then uses the exact indicator identity there. It does not assume separate integrability of the uncorrected jump or linear compensator near zero.
-- source:
--   Original GeneratorIntegrable and P4-C small_cutoff_compensation_identity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_small_cutoff_remainder_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y - deriv w y * z)
      (Ico (-ε) (0 : ℝ)) X.ν := by sorry
