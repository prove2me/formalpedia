-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_underbudget_violation_occurs_after_zero_horizon
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_underbudget_violation_occurs_after_zero_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:59:09.307374+00:00
-- url     : https://prove2.me/theorems/7a54237b-b5af-4154-b776-d6e7b2484090
-- title:
--   Every underbudget original BV zero-cap finite-horizon counterexample arises at a strictly positive horizon
-- statement:
--   For original Standing bounded-variation finite-jump-activity Lévy X with q>0 and any allowance W below exact reflected value drift/(q+ν(Iio 0).toReal), a finite natural horizon n strictly greater than zero has expected complete ruin-stopped Stieltjes payout greater than ENNReal.ofReal W. Proved 520c7065 supplies finite-horizon excess; Proved c96? More directly Proved 34cd52fc shows original zero-reserve admissible control has exactly zero expected complete Stieltjes cash at horizon zero; Proved 32b4ccb8 gives original zero-cap barrier admissibility. Since ENNReal.ofReal W≥0, the witness n cannot equal zero. This is formal conditional finite-horizon boundary-counterexample certification, retaining original Ω/P/𝓕/X.
-- source:
--   Proved 520c7065, 34cd52fc, 32b4ccb8, original ruinTime/paymentTimes/dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_underbudget_violation_occurs_after_zero_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUnder : W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :
    ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by sorry
