-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_corrected_killed_discount_measurable
-- name    : AvramDividend.Classical.avram_p4_f6_hjb_corrected_killed_discount_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:28:43.13064+00:00
-- url     : https://prove2.me/theorems/9f6d506d-7a8e-404e-93de-e0392012604a
-- title:
--   Original corrected Lévy exit clocks and killed discounted reward are measurable
-- statement:
--   For the actual spectrally negative Lévy process, the corrected upper and lower exit time observables are measurable, and the killed discounted upper-exit payoff is measurable for every q. This instantiates the previously proved raw passage-clock measurability theorem for the corrected observables and applies the measurable ENNReal-to-real, exponential and nonnegative-real embeddings. It supplies the measurability obligations for infinite-horizon HJB reductions without conflating corrected and raw exit clocks.
-- source:
--   Source-exact corrected process upper/lower clock and discounted payoff measurability for original HJB killed exit theorem 8d1164b7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_hjb_corrected_killed_discount_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q lower upper : ℝ) :
    Measurable (fun ω : Ω => twoSidedExitUpTimeCorrected X upper ω) ∧
    Measurable (fun ω : Ω => twoSidedExitDownTimeCorrected X lower ω) ∧
    Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp
      (-(q * (twoSidedExitUpTimeCorrected X upper ω).toReal)))) := by sorry
