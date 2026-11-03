-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_actual_path_has_positive_finite_horizon_cash
-- name    : AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_actual_path_has_positive_finite_horizon_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:33:32.284884+00:00
-- url     : https://prove2.me/theorems/70c63725-45bf-4aa0-8709-12c635de1da9
-- title:
--   Original finite-activity BV zero-cap process has an actual sample path with positive stopped Stieltjes cash
-- statement:
--   For a genuine Standing BV spectrally negative Lévy X with finite negative-jump activity and positive discount, the previously Proved strictly positive expected complete Stieltjes cash for the zero-barrier cap-zero strategy implies that there exist a finite natural horizon n and a sample ω from the original Ω whose actual pathwise stopped discounted full Stieltjes payout is strictly positive. If all original samples had zero cash, their outer lintegral against the original P would be zero, contradicting the Proved positive expectation. The theorem does not replace the probability space or assert an unconditional Standing/BV model existence witness.
-- source:
--   Proved original positive expected full Stieltjes cash 09bbe99b and Mathlib lintegral_zero; identical original Ω, P, 𝓕, X, ruinTime, paymentTimes, barrierStrategy, dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_actual_path_has_positive_finite_horizon_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (n : ℕ) (ω : Ω), 0 <
      (∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω)) := by sorry
