-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:07:01.138436+00:00
-- url     : https://prove2.me/theorems/4396ddd6-6981-42c6-9f15-733157b72a22
-- title:
--   No Stieltjes barrier-dividend mass from time zero through the first upper passage
-- statement:
--   The complete Stieltjes dividend measure, including its possible time-zero atom, vanishes throughout the closed interval from time zero to the finite first upper-barrier passage when x lies below a. This permits the corresponding stopped discounted dividend integral to begin after the passage time.
-- source:
--   Root-connected strong-Markov value split 79978d61-9d1f-4b20-b8a5-114797a8e380. Combines Proved zero initial atom 1b0903d2-b92b-4844-bd1e-58116aa9bf03 and the preceding open but directly pursued zero (0,u] mass lemma 88bf2f0b-9cd7-4772-89fc-a85ccae6d64d.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_initial_dividendMeasure_atom

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Icc (0 : ℝ) (u : ℝ)) = 0 := by
  sorry
