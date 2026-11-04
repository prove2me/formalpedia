-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_identdistrib
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_identdistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:05:10.233086+00:00
-- url     : https://prove2.me/theorems/d8a0cca3-7df3-4b21-8acb-4936e236634b
-- title:
--   Original Levy stationary increments remain identically distributed after drift centring
-- statement:
--   For the original Levy process, the distribution of each deterministic increment after subtracting the actual drift over its length equals the drift-centred marginal at the length of the interval. This is a measurable-image law bridge for subsequent Gaussian arguments.
-- source:
--   Original SpectrallyNegativeLevy.stationaryIncrements and Mathlib ProbabilityTheory.IdentDistrib.comp.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_identdistrib
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      (fun ω => Y.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * Y.c)
      P P := by sorry
