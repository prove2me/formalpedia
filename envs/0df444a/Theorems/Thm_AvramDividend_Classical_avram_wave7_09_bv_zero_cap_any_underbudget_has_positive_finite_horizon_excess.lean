-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_any_underbudget_has_positive_finite_horizon_excess
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_any_underbudget_has_positive_finite_horizon_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:47:55.98641+00:00
-- url     : https://prove2.me/theorems/520c7065-bf94-40f3-82e6-839f228ba664
-- title:
--   Any allowance below the exact BV zero-cap value fails at some finite original Stieltjes horizon
-- statement:
--   Fix the genuine original Standing bounded-variation finite-activity spectrally negative Lévy source and positive q. For every real allowance W strictly below its exact discounted zero-barrier reflected payout drift/(q+ν((−∞,0)).toReal), there exists a finite natural horizon n for which the original stopped expected complete Stieltjes payout strictly exceeds ENNReal.ofReal W. This is the contrapositive of Proved fa374bd0 with the strict order embedding of positive real exact value, using Proved positive drift 0432f641. It provides a formal finite-horizon counterexample for every underbudget, without asserting an unconditional existence of Standing BV source X.
-- source:
--   Proved fa374bd0, Proved 0432f641, pinned ENNReal.ofReal_lt_ofReal_iff, canonical original sample Ω/P/X, ruinTime, paymentTimes and dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_any_underbudget_has_positive_finite_horizon_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUnder : W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :
    ∃ n : ℕ, ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by sorry
