-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess17_original_zero_prestate_source_measurable
-- name    : AvramDividend.Classical.avram_bv_excess17_original_zero_prestate_source_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:11:01.460872+00:00
-- url     : https://prove2.me/theorems/6766afb6-3312-4d43-83c5-88ba0557ccfe
-- title:
--   Actual original BV prepayment zero-reserve event is measurable at every deterministic right-continuous filtration time
-- statement:
--   At each fixed original source time, the strict-left-limit controlled prepayment reserve is measurable under the right-continuous source filtration. Its zero-contact indicator is therefore a legitimate bounded predictable coefficient for a forthcoming compensated negative-mark count. The proof uses only already-proved original-process adaptedness, strict left limits and left-limit adaptedness, not an auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess17_original_zero_prestate_source_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s : ℝ≥0) :
    MeasurableSet[𝓕.rightCont s] {ω : Ω |
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) s = 0} := by sorry
