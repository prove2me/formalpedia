-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_continuous_renewal_density_with_canonical_kernel
-- name    : AvramDividend.Classical.bv_esscher_continuous_renewal_density_with_canonical_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:58:40.395857+00:00
-- url     : https://prove2.me/theorems/4a37beac-6718-417f-b4c0-18e0042486f3
-- title:
--   Continuous BV Esscher renewal density retaining the canonical divergent kernel
-- statement:
--   The exponentially tilted BV q-scale function admits a continuous locally integrable real renewal density, built explicitly from the canonical drift-normalised strict-tail kernel and its real convolution powers, under standing bounded-variation hypotheses without Lévy-measure absolute continuity.
-- source:
--   Source-derived strengthening of Proved bv_ac_esscher_continuous_renewal_density_representation, source SHA-256 6f0090d8b859b0015c8b090771c0512f67472af59dcf7e0f93a4b7cf036df75d, and using the pointwise canonical renewal-series data.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_renewal_kernel_series_data_with_pointwise
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_esscher_continuous_renewal_density_with_canonical_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < φ ∧ X.ψ φ = q ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      f = (fun y : ℝ =>
        b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y) ∧
      ContinuousOn f (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x, f y) := by sorry
