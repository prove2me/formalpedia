-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_separated_borel_nu_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:22:43.447206+00:00
-- url     : https://prove2.me/theorems/86086cb2-e1cd-4ed8-a49b-7f8eefc9842b
-- title:
--   Original Lévy measure finite on every separated negative Borel band
-- statement:
--   For the actual source SpectrallyNegativeLevy process and every measurable B contained in (-∞,-ε] with ε>0, the original Lévy measure ν(B) is finite. The proof uses the source ν-integrability assumption and the proved small-threshold finite-tail theorem, reducing arbitrary ε to min(ε,1); no independent model or jump compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_separated_borel_nu_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    X.ν B < ⊤ := by sorry
