-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_cash_witness_has_strictly_positive_horizon
-- name    : AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_cash_witness_has_strictly_positive_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:28:15.471749+00:00
-- url     : https://prove2.me/theorems/e4b40064-a0d3-4b93-8e35-53cce484c4ba
-- title:
--   BV finite-activity zero-cap reflected cash witness occurs strictly after horizon zero
-- statement:
--   In the exact original Standing bounded-variation spectrally negative Lévy source with finite total negative-jump activity and q>0, the zero-start zero-cap canonical reflected strategy has strictly positive expected complete discounted Stieltjes cash at a strictly positive integer horizon n. This refines the earlier positive-cash existence theorem by formally ruling out n=0 using the Proved original zero-horizon expected Stieltjes cash identity and genuine barrier admissibility. It certifies that the boundary failure arises at later payments and cannot be attributed to a time-zero atom.
-- source:
--   Proved 09bbe99b finite-horizon cash witness, Proved 34cd52fc zero-horizon expected payout, Proved 32b4ccb8 original barrier admissibility; original Ω, P, X, filtration, ruinTime, paymentTimes, dividendMeasure unchanged. No Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_cash_witness_has_strictly_positive_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ, 0 < n ∧ 0 <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by sorry
