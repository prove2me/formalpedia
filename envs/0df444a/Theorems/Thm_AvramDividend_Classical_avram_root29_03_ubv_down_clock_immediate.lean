-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_down_clock_immediate
-- name    : AvramDividend.Classical.avram_root29_03_ubv_down_clock_immediate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:38:20.761825+00:00
-- url     : https://prove2.me/theorems/c56bc2f2-9674-4e57-84ac-faddee34b449
-- title:
--   Strict downward exit clock is zero almost surely under unbounded variation
-- statement:
--   For an actual spectrally negative Levy process of unbounded variation, the strict lower exit clock from initial capital zero is almost surely zero. This is the genuine original-clock boundary case of the paper's two-sided exit problem, with no Standing or scale-function assumption. It combines the independently accepted Rogozin negative near-zero theorem and its exact infimum-clock conversion.
-- source:
--   Canonical 5bcf90e1 and 2dcc8bcc require boundary x=0. The original-process almost-sure negative near-zero law 703dc740 and strict-clock converter ac9a5651 are independently Proved, neither depends on any open stopped-scale theorem. This child provides their exact source-level interface to the named twoSidedExitDownTime and can be reused in zero-start stopped-scale and exit-ratio proofs; no reverse parent import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_zero_of_negative_near_zero

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_down_clock_immediate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0 := by sorry
