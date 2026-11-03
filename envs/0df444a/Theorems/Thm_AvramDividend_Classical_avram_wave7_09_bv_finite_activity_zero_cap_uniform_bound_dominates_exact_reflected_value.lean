-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
-- name    : AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:31:35.559333+00:00
-- url     : https://prove2.me/theorems/fa374bd0-b4e4-4d3f-9593-f2f7e5a27d2f
-- title:
--   Sharp necessary boundary allowance for a uniform original BV zero-cap reflected dividend bound
-- statement:
--   For an original Standing bounded-variation spectrally negative Lévy process with finite negative-jump activity, positive discount and zero-barrier strategy started at x=0 under cap C=0, any common upper bound ENNReal.ofReal W on all finite natural-horizon expected discounted complete Stieltjes payouts must dominate the exact infinite-horizon reflected dividend value ENNReal.ofReal(X.drift/(q+(ν(Iio 0)).toReal)). This is a sharp quantitative necessary condition for such a uniform bound, obtained from the Proved original value identity and finite-horizon-to-value bridge. No claim it is necessary for arbitrary policies or sufficient for all verification candidates.
-- source:
--   Proved 6f73f927 exact original finite-activity zero-reflected first-jump payout, Proved 11b589b7 barrier own value identity, Proved 32b4ccb8 source cap0 admissibility, Proved dc933bd8 finite-horizon-to-value bridge. No Open imports or replacement stochastic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) :
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤
    ENNReal.ofReal W := by sorry
