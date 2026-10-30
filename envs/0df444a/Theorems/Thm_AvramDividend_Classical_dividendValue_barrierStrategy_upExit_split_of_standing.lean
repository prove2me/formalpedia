-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_upExit_split_of_standing
-- name    : AvramDividend.Classical.dividendValue_barrierStrategy_upExit_split_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T05:08:25.967601+00:00
-- url     : https://prove2.me/theorems/79978d61-9d1f-4b20-b8a5-114797a8e380
-- title:
--   Standing-only strong-Markov up-exit splitting of the barrier-strategy dividend value
-- statement:
--   For a spectrally negative Levy process under the standing assumptions with 0 <= x <= a and a > 0, the expected discounted dividends of the barrier strategy at level a started from x equal the discounted two-sided up-exit indicator integral times the barrier-strategy value started from a. Same strong-Markov content as sibling 5f7f43e1 but with the vacuous scale-function hypotheses (W, hW) removed, since neither appears in the conclusion and the consuming parent 8fc83520 carries no scale function in context.
-- source:
--   Avram, Palmowski and Pistorius (2007) barrier dividend identities; W-free correction of the strong-Markov splitting step for parent 8fc83520-78bb-4a8c-a394-12b04a096b66 within mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. The published sibling 5f7f43e1 carries unused (W, hW) hypotheses that the W-free parent context cannot discharge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendValue_barrierStrategy_upExit_split_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * dividendValue X q a (barrierStrategy X a a) := by sorry
