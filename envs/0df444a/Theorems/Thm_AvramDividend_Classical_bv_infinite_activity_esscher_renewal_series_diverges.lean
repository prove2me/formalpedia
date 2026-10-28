-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_esscher_renewal_series_diverges
-- name    : AvramDividend.Classical.bv_infinite_activity_esscher_renewal_series_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:21:41.221721+00:00
-- url     : https://prove2.me/theorems/b9fc5e94-f7a2-47b4-9968-f1792d409397
-- title:
--   Canonical BV infinite activity forces full Esscher causal renewal series to diverge at zero
-- statement:
--   Under standing bounded-variation and infinite negative-jump activity assumptions, construct the drift-normalised canonical Esscher kernel, full real convolution powers and their nonnegative summable renewal-density series. The positive first term is the kernel, which diverges at zero, hence the entire real renewal series diverges at zero. This supplies the exact density blow-up required for the infinite right scale-derivative theorem.
-- source:
--   Proved drift-normalised kernel divergence, causal_subunit_renewal_full_real_power_package, renewal_density_series_summable_of_geometric_power_bound and esscher_positive_renewal_tsum_tendsto_top.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Infinite jump activity makes the full positive causal Esscher renewal density diverge. -/
theorem bv_infinite_activity_esscher_renewal_series_diverges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ),
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ κ x) ∧
      Integrable κ volume ∧
      (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      Tendsto (fun x : ℝ => ∑' n : ℕ, F n x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
