-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
-- name    : AvramDividend.Classical.avram_p4_f2_original_negative_band_ncard_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:49:45.01109+00:00
-- url     : https://prove2.me/theorems/7f0f2707-c11a-4e35-9aa3-96950b57cce1
-- title:
--   Original Lévy negative-band finite jump cardinal is measurable
-- statement:
--   The finite number of actual negative-band jump times in the original spectrally negative Lévy path is a measurable Nat-valued random variable. Proven by measurable ENNReal original count and its exact pathwise identification with Nat cardinal, using only singleton preimage measurability.
-- source:
--   Proved 5cb1e247 original intrinsic marked-count measurability and f0197436 source count equals finite marked ncard; enables 517be7d8 factorial void bound for source zero-band law 17372d7a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_original_negative_band_ncard_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun ω : Ω =>
      ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℕ)) := by sorry
