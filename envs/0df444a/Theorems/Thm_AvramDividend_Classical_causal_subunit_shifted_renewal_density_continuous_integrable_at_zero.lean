-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
-- name    : AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:48:08.196885+00:00
-- url     : https://prove2.me/theorems/84fff55b-5a1e-48f8-8c2c-590567fde009
-- title:
--   Constructed subunit causal renewal density is continuous and scaled-integrable from zero
-- statement:
--   A continuous antitone nonnegative causal kernel of mass 0<rho<1 admits full-real convolution powers. Their index-shifted renewal series is continuous on positive times and, after arbitrary scalar multiplication, interval-integrable from zero to every positive time. Combines the established geometric power bounds, L1 extension, renewal-series continuity and zero-endpoint integrability as a usable deterministic bounded-variation Esscher prerequisite.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_at_zero
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_causal_shifted_renewal_density_interval_integrable_at_zero
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
    (κ : ℝ → ℝ) (ρ b : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      ContinuousOn
        (fun x : ℝ => ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y)
          volume 0 x) := by sorry
