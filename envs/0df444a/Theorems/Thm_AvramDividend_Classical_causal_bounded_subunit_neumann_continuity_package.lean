-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_bounded_subunit_neumann_continuity_package
-- name    : AvramDividend.Classical.causal_bounded_subunit_neumann_continuity_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:52:46.618986+00:00
-- url     : https://prove2.me/theorems/76ad7e69-c38c-4662-badd-63dab9b11fea
-- title:
--   Construct continuous nonnegative geometrically summable causal convolution powers
-- statement:
--   For a continuous, bounded, globally nonnegative causal kernel of positive total mass rho<1, construct its nonnegative causal convolution powers. Every power is integrable and continuous, vanishes at nonpositive arguments, and the pointwise Neumann series converges everywhere and is continuous on the nonnegative half-line. This combines the proved geometric truncated-mass, convolution continuity, uniform sup-bound and Weierstrass M-test lemmas.
-- source:
--   Proved causal_positive_convolution_powers_geometric_truncated_mass, causal_Ioc_convolution_powers_continuous_of_bounded_kernel, causal_power_sup_geometric_from_truncated_mass and causal_neumann_series_continuous_of_uniform_geometric_bound.

import Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_continuous_of_bounded_kernel
import Theorems.Thm_AvramDividend_Classical_causal_continuous_product_integrable_full
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
import Theorems.Thm_AvramDividend_Classical_causal_power_sup_geometric_from_truncated_mass
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_continuous_of_uniform_geometric_bound
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_bounded_subunit_neumann_continuity_package
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκbounded : BddAbove (Set.range (fun x : ℝ => ‖κ x‖)))
    (hκi : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hκmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, Continuous (F n)) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => F n x)) ∧
      ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici 0) := by sorry
