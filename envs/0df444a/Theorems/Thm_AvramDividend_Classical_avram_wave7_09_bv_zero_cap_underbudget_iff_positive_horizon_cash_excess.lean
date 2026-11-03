-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_underbudget_iff_positive_horizon_cash_excess
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_underbudget_iff_positive_horizon_cash_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:26:57.16479+00:00
-- url     : https://prove2.me/theorems/fd006bc5-4578-4c9e-855e-d4d485a15daf
-- title:
--   Exact iff: original BV zero-cap underbudget occurs at some strictly positive finite Stieltjes horizon
-- statement:
--   For the same original Standing finite-negative-jump-activity bounded-variation Lévy process, q>0 and any real allowance W at zero reserve and zero cap, the strict inequality W<drift/(q+ν(Iio0).toReal) is equivalent to the existence of a strictly positive finite natural horizon n with expected original complete stopped Stieltjes cash greater than ENNReal.ofReal W. Proved 7a54237b supplies the positive finite-horizon excess from underbudget. Conversely Proved fdf4348f gives uniform bound for every horizon whenever W≥the exact reflected threshold, contradicting any strict excess. This upgrades a one-sided conditional counterexample to an exact necessary-and-sufficient boundary classification without asserting unconditional existence of such X.
-- source:
--   Proved 7a54237b, fdf4348f; exact canonical source Ω/P/𝓕/X, ruinTime, paymentTimes, dividendMeasure, barrierStrategy. No Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_underbudget_iff_positive_horizon_cash_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ) :
    (W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ↔
    ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by sorry
