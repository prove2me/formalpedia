-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_uniform_ennreal_budget_iff_exact_reflected_value_bound
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_uniform_ennreal_budget_iff_exact_reflected_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:28:34.942552+00:00
-- url     : https://prove2.me/theorems/d326509c-4e27-48d2-abd3-3274376998d8
-- title:
--   Exact BV zero-cap uniform original Stieltjes boundary budget criterion for every ENNReal allowance
-- statement:
--   For a genuine Standing bounded-variation spectrally negative Lévy process with finite negative-jump intensity at cap C=0 and initial reserve 0, positive discount q, and any extended-nonnegative allowance A including ⊤, every finite natural-horizon expected original complete stopped Stieltjes cash payout is at most A if and only if the exact reflected value ENNReal.ofReal(drift/(q+ν(Iio0).toReal)) is at most A. Forward uses Proved original cap-zero barrier admissibility 32b4ccb8 and Proved finite-horizon-to-value bridge dc933bd8 with Proved exact reflected value identity 6f73f927 and 11b589b7. Reverse uses new Proved all-horizon domination 7c3bf4db. This extends the real sharp threshold fdf4348f to arbitrary ENNReal budgets, retaining original Ω/P/𝓕/X and the true payout.
-- source:
--   Proved 7c3bf4db, dc933bd8, 6f73f927, 11b589b7 and 32b4ccb8. No Open imports and no replacement model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_uniform_ennreal_budget_iff_exact_reflected_value_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤ A) ↔
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤ A := by sorry
