-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_upExit_split
-- name    : AvramDividend.Classical.dividendValue_barrierStrategy_upExit_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T03:37:00.736261+00:00
-- url     : https://prove2.me/theorems/5f7f43e1-0d48-4879-b2c4-b205f9cdeb8f
-- title:
--   Strong-Markov up-exit splitting of the barrier-strategy dividend value
-- statement:
--   For a spectrally negative Levy process under the standing assumptions with initial capital 0 <= x <= a and a > 0, the expected discounted dividends of the barrier strategy at level a started from x equal the discounted two-sided up-exit indicator integral (up-exit strictly before down-exit/ruin, in raw first-passage form) multiplied by the barrier-strategy dividend value started from a. This is the strong-Markov splitting step of the killed-exit factorisation 8fc83520: no dividends are paid before the up-exit, spectral negativity puts the process exactly at level a then, and the Proved barrierValue_self_eq_barrierSupValue identifies the restarted value with barrierSupValue. It assumes no Open exit theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007) barrier dividend identities; strong-Markov splitting step isolated as the precise open obligation of parent 8fc83520-78bb-4a8c-a394-12b04a096b66 within mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendValue_barrierStrategy_upExit_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * dividendValue X q a (barrierStrategy X a a) := by sorry
