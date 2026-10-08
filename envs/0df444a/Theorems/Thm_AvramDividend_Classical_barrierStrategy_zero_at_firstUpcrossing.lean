-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_at_firstUpcrossing
-- name    : AvramDividend.Classical.barrierStrategy_zero_at_firstUpcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:28:47.115998+00:00
-- url     : https://prove2.me/theorems/feaa4d37-5e40-4b4b-8f34-fd1c5b6d7b29
-- title:
--   No dividend jump at an attained first upward barrier crossing
-- statement:
--   At the finite first strict upcrossing time u of the pre-dividend surplus level a-x≥0, the barrier strategy has paid exactly zero cumulative dividends, including at u. No-positive-jump paths attain the threshold at u, while all earlier levels are below or equal to it. The published zero-before-upcrossing theorem then gives Lᵃ_u=0. The result removes a potential first-passage dividend atom from the stopped Stieltjes reward when proving the barrier-value strong-Markov factorisation. All imported dependencies are already fully Proved.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 first-passage argument; canonical Proved project lemmas firstUpcrossing_prethreshold_le, firstUpcrossing_value_eq_threshold, barrierStrategy_zero_before_upcrossing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_zero_at_firstUpcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞))) :
    barrierStrategy X x a u ω = 0 := by sorry
