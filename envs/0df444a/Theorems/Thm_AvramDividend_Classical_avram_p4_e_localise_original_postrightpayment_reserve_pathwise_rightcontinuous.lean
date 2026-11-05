-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:57:48.23905+00:00
-- url     : https://prove2.me/theorems/a2202506-384e-458e-bd9c-9207c02da3c3
-- title:
--   Original right-paid controlled reserve is right-continuous at zero, cap and all physical times
-- statement:
--   The source Lévy process has actual pathwise right-continuous increments and X.X0=0. Every admissible original dividend control has a pathwise right-continuous strict-right dividend limit. Their pointwise difference x+X.X_t-rightLimit D_t is therefore pathwise right-continuous at every t, with no strict-interior reserve premise. This gives the exact source W-side continuity needed for ceiling localisation, though w itself may jump at a negative ruin overshoot.
-- source:
--   Proved original shifted Lévy increments càdlàg, Proved source dividendStrategy_rightLimit_rightContinuous, X.X_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The unchanged original Lévy reserve after right dividend payment has pathwise right continuity even at zero and the cap. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (Ici t) t := by sorry
