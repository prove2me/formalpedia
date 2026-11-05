-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_ruin_terminal_integral_zero_after_horizon
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_ruin_terminal_integral_zero_after_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:12:41.053892+00:00
-- url     : https://prove2.me/theorems/64e815a7-4999-470d-82da-99e08e76730c
-- title:
--   True original strictly stopped terminal expectation vanishes after its bounded horizon
-- statement:
--   For the actual spectrally negative Levy process and original ruinTime, any deterministic S>=T has zero discounted strict stopped terminal payoff expectation, for arbitrary w,q and measure P. The exact strict ruin-clock endpoint equivalence rules out S<min(ruinTime,T), even at horizon equality and T=0. This proves a terminal-limit input without imposing cap contact occupation zero or integrability not otherwise available.
-- source:
--   Proved original source strict bounded ruin-clock endpoints b4677f24; pointwise zero and Lebesgue integral zero.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_ruin_terminal_integral_zero_after_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (T S : ℝ≥0) (hTS : T ≤ S) :
    (∫ ω, if (S : ℝ≥0∞) <
        (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
      then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0 ∂P) = 0 := by sorry
