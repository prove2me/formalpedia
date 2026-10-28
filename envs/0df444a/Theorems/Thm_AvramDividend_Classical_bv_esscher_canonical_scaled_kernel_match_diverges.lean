-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_kernel_match_diverges
-- name    : AvramDividend.Classical.bv_esscher_canonical_scaled_kernel_match_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:40:31.993662+00:00
-- url     : https://prove2.me/theorems/48c1177a-9449-4006-ad0c-0584fd5c69ce
-- title:
--   Exact canonical BV Esscher scale-kernel measure match with infinite origin blow-up
-- statement:
--   Under standing BV infinite Lévy activity, show that the unique explicit drift-normalised Esscher tail kernel simultaneously supplies the canonical positive-subunit scaled jump-tail measure and tends to positive infinity as the argument approaches zero from the right. This is the exact kernel needed by the geometric scale primitive.
-- source:
--   Compose independently Proved bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise and bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity using their identical explicit pointwise strict-tail formula.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_canonical_scaled_kernel_match_diverges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ),
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      (ENNReal.ofReal X.drift)⁻¹ •
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)}) =
        (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal (κ t)) ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
