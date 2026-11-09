-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_reset_amount_clock_measurable
-- name    : AvramDividend.Classical.avram_bv_tail13_original_reset_amount_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:28:17.777277+00:00
-- url     : https://prove2.me/theorems/70cabc2a-8f0d-4e5d-852f-bdb2ae696ecc
-- title:
--   Clock measurability of original Levy reserve-reset amount
-- statement:
--   For the exact original spectrally negative Levy process and its filtration, the clipped nonnegative reserve evaluated at a deterministic clock is measurable in the information at that clock. This supplies the genuine original-process payment measurability required by the single-clock adapted dividend strategy.
-- source:
--   The source SpectrallyNegativeLevy provides X.adapted. At a deterministic clock, the sum of fixed initial reserve and X.X s is filtration-measurable, and taking max with zero preserves measurability.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_original_reset_amount_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (s : ℝ≥0) :
    Measurable[𝓕 s] (fun ω => max (x + X.X s ω) (0 : ℝ)) := by sorry
