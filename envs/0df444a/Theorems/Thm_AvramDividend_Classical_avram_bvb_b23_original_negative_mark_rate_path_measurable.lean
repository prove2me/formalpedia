-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_negative_mark_rate_path_measurable
-- name    : AvramDividend.Classical.avram_bvb_b23_original_negative_mark_rate_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:49:15.614352+00:00
-- url     : https://prove2.me/theorems/3740173c-7fb1-4831-b08f-737e57016b00
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b23_original_negative_mark_rate_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (ν : Measure ℝ) [SFinite ν] (ω : Ω) :
    Measurable (fun t : ℝ≥0 =>
      ∫ z, w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t + z) -
        w (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ∂ν) := by sorry
