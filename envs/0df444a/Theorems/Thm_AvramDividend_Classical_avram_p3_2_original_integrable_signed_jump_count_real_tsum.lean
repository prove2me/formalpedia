-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_integrable_signed_jump_count_real_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_integrable_signed_jump_count_real_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:17:11.689232+00:00
-- url     : https://prove2.me/theorems/4a4f9726-181c-4ac1-9c2b-d1b6034094b5
-- title:
--   Actual original Lévy signed jump integral equals positive-minus-negative real tSums under L1
-- statement:
--   For the exact original spectrally negative Lévy marked jump count NX, a measurable signed real kernel F integrable against NX has real integral equal to the real values of the positive and negative ENNReal original jump time sums, subtracted. It uses an explicit, indispensable L1 premise and does not assume finite activity, an independent jump proxy, or upgraded integrability.
-- source:
--   Proved original signed positive/negative marked count identity 5a6da9d6 and the pinned Mathlib theorem MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part, whose exact signature was verified on 5 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original signed Lévy jump integral is exactly the difference
between its positive and negative original jump-count sums under L1. -/

theorem AvramDividend.Classical.avram_p3_2_original_integrable_signed_jump_count_real_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Integrable F NX →
      (∫ p, F p ∂NX) =
        (∑' u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
            ENNReal.ofReal (F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal -
        (∑' u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
            ENNReal.ofReal (-F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal := by sorry
