-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_every_finite_horizon_below_exact_reflected_value
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_every_finite_horizon_below_exact_reflected_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:18:28.1372+00:00
-- url     : https://prove2.me/theorems/7c3bf4db-207f-4572-baa7-1dfafbbe175c
-- title:
--   Every finite original BV zero-cap reflected dividend cash is below the exact first-jump value
-- statement:
--   Under the original Standing bounded-variation finite-negative-jump-activity spectrally negative Lévy process, positive discount and zero-start cap-zero reflected barrier strategy, every finite natural-horizon expected complete stopped Stieltjes dividend cash is bounded by the exact infinite-horizon reflected value ENNReal.ofReal(drift/(q+ν(Iio0).toReal)). Proved dividendValue_eq_iSup_truncated 3b737955 identifies the original dividendValue with the supremum of those finite-horizon expected cash terms, and Proved reflected first-jump value 6f73f927 with barrierValue identity 11b589b7 computes the supremum. This supplies the missing sufficient half of the sharp zero-cap uniform bound threshold.
-- source:
--   Exact Ω/P/𝓕/X, original barrierStrategy, ruinTime/paymentTimes/dividendMeasure. Imports only Proved 3b737955, 6f73f927, 11b589b7 and 32b4ccb8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_every_finite_horizon_below_exact_reflected_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
