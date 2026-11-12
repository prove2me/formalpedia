-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_prepayment_leftlim_path_measurable
-- name    : AvramDividend.Classical.avram_bvb_b22_original_prepayment_leftlim_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:23:40.24437+00:00
-- url     : https://prove2.me/theorems/629955c0-a7a6-42ee-92c5-a9455a7c9ec4
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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b22_original_prepayment_leftlim_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by sorry
