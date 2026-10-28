-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_infinite_activity_full_scale_renewal_series
-- name    : AvramDividend.Classical.bv_esscher_infinite_activity_full_scale_renewal_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:47:31.046935+00:00
-- url     : https://prove2.me/theorems/14a1f322-97a4-4bb7-8da7-f654d7a6a907
-- title:
--   BV infinite activity makes the exact positive-scale renewal series diverge
-- statement:
--   Under standing bounded variation and infinitely many negative jumps, the exact drift-normalised causal Esscher renewal series appearing in the positive q-scale function's integral representation diverges at zero. Retain its convolution powers, non-negativity, integral identity and positive normalisation coefficient.
-- source:
--   Composition of independently Proved exact scale primitive with pointwise kernel (72f2341a-9e14-4cef-a6ae-f6fc7663097e), normalized kernel divergence (b1847f74-b00c-434e-9adf-fd389e44ae34) and deterministic causal renewal series summability and divergence lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_infinite_activity_full_scale_renewal_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < b ∧
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
