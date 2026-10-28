-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_pointwise_series_summable
-- name    : AvramDividend.Classical.causal_subunit_renewal_pointwise_series_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:20:52.445839+00:00
-- url     : https://prove2.me/theorems/bd333dd0-5dff-4ee6-8d34-469800812312
-- title:
--   Summability of causal subunit renewal convolution powers at positive times
-- statement:
--   A continuous nonnegative antitone causal kernel with positive mass rho below one has convolution powers satisfying the renewal recursion, and their series converges absolutely at every positive time. This combines the proved causal renewal power package with the quadratic-geometric summability bound and directly supports BV Esscher renewal densities.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_renewal_pointwise_series_summable
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρone : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ t : ℝ, t ≤ 0 → κ t = 0)
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s : ℝ, κ s * F n (x - s) ∂volume) ∧
      (∀ x : ℝ, 0 < x → Summable (fun n : ℕ => F n x)) := by sorry
