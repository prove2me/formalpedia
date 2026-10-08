-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
-- name    : AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:11:05.476793+00:00
-- url     : https://prove2.me/theorems/8fc83520-78bb-4a8c-a394-12b04a096b66
-- title:
--   Barrier dividend value factors into killed first passage and boundary reflected-supremum value
-- statement:
--   For a strictly positive constant barrier a and initial capital 0≤x≤a, the expected discounted dividends of the barrier regulator equal the discounted probability-weighted upward crossing of X above a−x strictly before X falls below −x, multiplied by the expected discounted running-supremum dividends at boundary level a. This isolates the strong Markov, no-positive-overshoot and dividend-measure time-shift component of Proposition 1 before the independent, already Proved deterministic identification of barrierSupValue X a q with the dividend value of the barrier strategy started from a. It uses only published Definition modules, not the Open two_sided_exit_before_ruin_identity theorem or a local definition shadow.
-- source:
--   Avram, Palmowski and Pistorius, On the Optimal Dividend Problem for a Spectrally Negative Levy Process I, Proposition 1 and the first-passage factorisation in Section 3.3. Theorem isolates strong Markov and stopped-reward factorisation from the boundary-value scale-function ratio.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_value_eq_killed_exit_mul_supValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * barrierSupValue X a q := by sorry

end AvramDividend.Classical
