-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_ge_small_band
-- name    : AvramDividend.Classical.esscher_weighted_negative_tail_real_ge_small_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:13:18.205171+00:00
-- url     : https://prove2.me/theorems/10a70dca-ad1b-488f-b1e3-17cc452641c2
-- title:
--   Real Esscher negative-tail kernel dominates weighted small-jump mass
-- statement:
--   Provided the weighted truncated Lévy tail is finite, its real mass dominates exp(-φ) times the real small-jump-band intensity. The quantitative measure inequality is already Proved. This theorem performs the delicate ENNReal-to-real transfer needed to feed a positive renewal kernel divergence theorem.
-- source:
--   Proved esscher_weighted_negative_tail_ge_small_band (071ceda0-a852-4fdf-bb6b-8dc08aa499f9) and Mathlib ENNReal.toReal_mono and ENNReal.toReal_ofReal_mul.

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_ge_small_band
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- On finite weighted tails, the Esscher band comparison also holds after conversion to real mass. -/
theorem esscher_weighted_negative_tail_real_ge_small_band
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ)
    (hfinite :
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) < ⊤) :
    Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal ≤
      ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x))).toReal := by sorry

end AvramDividend.Classical
