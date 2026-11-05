-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:24:15.541286+00:00
-- url     : https://prove2.me/theorems/c5058357-6739-46a6-8269-33866022b530
-- title:
--   Original admissible Lévy reserve prestate is ambient measurable
-- statement:
--   For the literal original controlled reserve left limit x+X.X-rightLimit D with genuine admissibility, prove ambient time-product measurability by combining its previously proved source strong predictability and the right-continuous predictable sigma-algebra's inclusion in the ambient product sigma-algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) := by sorry
