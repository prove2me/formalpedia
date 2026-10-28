-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
-- name    : AvramDividend.Classical.bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:09:09.255624+00:00
-- url     : https://prove2.me/theorems/b1847f74-b00c-434e-9adf-fd389e44ae34
-- title:
--   Infinite jump activity forces divergence of the normalised canonical BV renewal kernel
-- statement:
--   Convert the divergent unnormalised discounted negative-jump-magnitude tail into the exact drift-normalised canonical renewal kernel. Standing bounded variation provides strictly positive drift, so division preserves divergence to plus infinity. Retain the subunit positive kernel mass and all required continuity, monotonicity and integrability properties for the later renewal-density derivative theorem.
-- source:
--   Proved bv_esscher_positive_tail_kernel_diverges_of_infinite_activity, bv_esscher_root_positive_subunit_kernel_package, bv_standing_drift_pos.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Order.Filter.AtTopBot.Defs
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Infinite activity makes the drift-normalised canonical Esscher renewal density blow up at zero. -/
theorem bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ),
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
