-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_tendsto_top_of_small_band
-- name    : AvramDividend.Classical.esscher_weighted_negative_tail_real_tendsto_top_of_small_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:13:11.572576+00:00
-- url     : https://prove2.me/theorems/3c0fe1fa-a4f1-4229-ae8c-b7a56e1493ec
-- title:
--   Esscher weighted negative-tail intensity diverges whenever truncated weighted tails are finite
-- statement:
--   Let a measure on signed jump magnitudes have finite far-negative intensity, finite negative-tail mass at every positive truncation, and negative-tail real mass diverging as the truncation approaches zero. For a nonnegative Esscher tilt, if the weighted truncated negative-tail masses remain finite, their real masses likewise diverge. The result combines already Proved uniform Esscher density lower bounds on the small band and small-band divergence. This is a conditional measure-theoretic transfer lemma without assumptions on a stochastic process.
-- source:
--   Canonical Proved esscher_weighted_negative_tail_ge_small_band and negative_jump_small_band_tendsto_top; pinned Mathlib ENNReal.toReal_mono, toReal_mul and Filter.tendsto_atTop.

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_ge_small_band
import Theorems.Thm_AvramDividend_Classical_negative_jump_small_band_tendsto_top
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.esscher_weighted_negative_tail_real_tendsto_top_of_small_band
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfar : ν (Iic (-1 : ℝ)) < ⊤)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (hweighted : ∀ x : ℝ, 0 < x →
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) < ⊤)
    (htail : Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun x : ℝ =>
      ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
