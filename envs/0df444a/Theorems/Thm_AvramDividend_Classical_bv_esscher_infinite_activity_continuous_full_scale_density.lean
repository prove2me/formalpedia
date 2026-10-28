-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_infinite_activity_continuous_full_scale_density
-- name    : AvramDividend.Classical.bv_esscher_infinite_activity_continuous_full_scale_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:12:15.782446+00:00
-- url     : https://prove2.me/theorems/04a88464-228a-4690-acb6-71bec712a9e5
-- title:
--   Positive continuous BV Esscher scale-renewal density with infinite origin growth
-- statement:
--   Under standing bounded variation and infinite negative-jump activity, the exact Esscher q-scale renewal density is continuous on the positive half-line, locally integrable, and built with a strictly positive normalisation. Its nonnegative convolution series diverges at the origin, with the same canonical Lévy kernel and scale integral identity.
-- source:
--   Source-derived strengthening of Proved bv_esscher_infinite_activity_full_scale_renewal_series (candidate 16092), adding the Proved causal renewal-density continuity lemma and retaining its exact positive-coefficient scale representation.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_infinite_activity_continuous_full_scale_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < b ∧
      ContinuousOn
        (fun x : ℝ => b * ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x,
            (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)) ∧
      Tendsto (fun x : ℝ => ∑' n : ℕ, F n x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
