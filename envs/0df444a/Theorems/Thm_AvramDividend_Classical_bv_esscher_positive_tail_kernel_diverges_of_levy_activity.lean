-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_diverges_of_levy_activity
-- name    : AvramDividend.Classical.bv_esscher_positive_tail_kernel_diverges_of_levy_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:38:36.019259+00:00
-- url     : https://prove2.me/theorems/c1045080-f2e5-4741-a12c-200ce2472e26
-- title:
--   The canonical BV Esscher renewal kernel is positive, integrable and diverges at zero
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with a positive Esscher root, finite Lévy quadratic moment and infinite negative-jump activity, exhibit one canonical positive-magnitude Esscher strict-tail kernel that is continuous and antitone on the positive axis, nonnegative, integrable, supported on nonnegative times and diverges as t decreases to zero. This preserves the identical kernel witness used in the canonical geometric scale representation.
-- source:
--   Composition of Proved bv_esscher_positive_tail_kernel_shape_of_root (61873c37), negative_jump_real_tail_tendsto_top (2cde304a), negative_jump_truncation_measure_finite (16a2d301), and esscher_positive_magnitude_tail_real_tendsto_top (940a0338).

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_shape_of_root
import Theorems.Thm_AvramDividend_Classical_esscher_positive_magnitude_tail_real_tendsto_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Mathlib.MeasureTheory.Measure.WithDensity

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The same canonical positive BV jump-tail kernel has the regularity and divergence properties. -/
theorem bv_esscher_positive_tail_kernel_diverges_of_levy_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
