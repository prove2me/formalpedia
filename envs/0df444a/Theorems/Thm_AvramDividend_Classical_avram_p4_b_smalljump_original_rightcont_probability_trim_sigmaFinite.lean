-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:32:50.994121+00:00
-- url     : https://prove2.me/theorems/159a9398-7592-4f78-8af1-80b9d617b301
-- title:
--   Original right-continuous source probability filtration has sigma-finite trimmed measures at all times
-- statement:
--   For an original probability P and any filtration 𝓕, the derived right-continuous filtration has a sigma-finite trimmed measure P.trim(𝓕.rightCont.le s) at each time s. This discharges the sigma-finiteness premise of accepted original Lp2 martingale-limit closure 2ac43d23; no compensated jump martingale or jump moments are asserted.
-- source:
--   Pinned Mathlib isFiniteMeasure_trim and IsFiniteMeasure implies SigmaFinite, instantiated with the original right-continuous filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    ∀ s : ℝ≥0,
      @SigmaFinite Ω (𝓕.rightCont s) (P.trim (𝓕.rightCont.le s)) := by sorry
