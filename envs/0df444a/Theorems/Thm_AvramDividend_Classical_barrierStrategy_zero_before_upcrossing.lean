-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
-- name    : AvramDividend.Classical.barrierStrategy_zero_before_upcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T15:08:29.149135+00:00
-- url     : https://prove2.me/theorems/c82607cc-0acf-4529-96b1-d091dee02db5
-- title:
--   Barrier strategy pays nothing before its first upward passage
-- statement:
--   For an initial capital x and barrier a, if the path of the spectrally negative Lévy process stays below the threshold a-x throughout [0,t], then the cumulative barrier dividends at time t are exactly zero. This pathwise lemma supplies the zero-pre-passage contribution for the strong-Markov barrier value factorisation.
-- source:
--   Definition of barrierStrategy in Def_AvramDividend_Classical_DividendStrategy, and the strong-Markov argument in Avram, Palmowski and Pistorius (2007), Proposition 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_zero_before_upcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (t : ℝ≥0) (ω : Ω)
    (hbelow : ∀ s : ℝ≥0, s ≤ t → X.X s ω ≤ a - x) :
    barrierStrategy X x a t ω = 0 := by sorry
