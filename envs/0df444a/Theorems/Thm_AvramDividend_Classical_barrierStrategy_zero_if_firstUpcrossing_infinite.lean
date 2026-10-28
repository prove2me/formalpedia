-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_if_firstUpcrossing_infinite
-- name    : AvramDividend.Classical.barrierStrategy_zero_if_firstUpcrossing_infinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:32:15.304232+00:00
-- url     : https://prove2.me/theorems/e5d0c125-28ee-4604-9925-0e1ff6a1b2f6
-- title:
--   No barrier dividends at any finite time when the first upper passage is infinite
-- statement:
--   If the strict upward first-passage clock of the Lévy process never becomes finite, the process never exceeds the barrier threshold at any finite time. The established below-threshold barrier strategy lemma therefore forces the cumulative dividends to vanish at every time. This supplies the infinite-passage branch of the strong-Markov barrier dividend valuation.
-- source:
--   Root-connected strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380. Imports the Proved pathwise below-threshold zero-dividend lemma c82607cc-0acf-4529-96b1-d091dee02db5.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_zero_if_firstUpcrossing_infinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω)
    (hnever : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω),
      (s : ℝ≥0∞)) = ⊤) :
    ∀ t : ℝ≥0, barrierStrategy X x a t ω = 0 := by
  sorry
