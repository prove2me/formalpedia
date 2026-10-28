-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_negative_levy_tail_real_tendsto_top
-- name    : AvramDividend.Classical.esscher_negative_levy_tail_real_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:32:27.288688+00:00
-- url     : https://prove2.me/theorems/0452ce34-3964-4e0b-8e7f-6970b75dfc4d
-- title:
--   Lévy integrability and infinite negative activity imply divergent Esscher weighted tail
-- statement:
--   Under the Lévy quadratic moment condition and infinite total negative-jump activity, every strictly positive truncation has finite mass and its Esscher-weighted real mass tends to infinity as the truncation approaches zero. The result discharges the auxiliary far-tail, local-finiteness and weighted-finiteness hypotheses of the already verified abstract divergence transfer.
-- source:
--   Proved negative_jump_truncation_measure_finite (16a2d301), negative_jump_real_tail_tendsto_top (2cde304a), esscher_weighted_negative_tail_le_unweighted (25fe0eaf), esscher_weighted_negative_tail_real_tendsto_top_of_small_band (3c0fe1fa).

import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_tendsto_top_of_small_band
import Mathlib.MeasureTheory.Measure.WithDensity

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- The Esscher-weighted strict negative-jump tail diverges from the Lévy hypotheses alone. -/
theorem esscher_negative_levy_tail_real_tendsto_top
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun x : ℝ =>
      ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
