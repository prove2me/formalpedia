-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_l1_resolvent
-- name    : AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:53:37.457011+00:00
-- url     : https://prove2.me/theorems/2178ea9c-4397-4849-8b65-d03d111253c3
-- title:
--   Causal subunit renewal density is globally L1 on the positive axis with exact resolvent mass
-- statement:
--   Under an antitone continuous causal kernel of mass 0<rho<1, construct recursive real-line convolution powers whose whole summed renewal density is integrable on (0,infinity), with integral rho/(1-rho). Strengthens the proved total-mass result by actual L1 integrability, enabling justified renewal Laplace transforms, absolute continuity and measure-density manipulations.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_total_mass_sum
import Mathlib.Analysis.SpecificLimits.Basic

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent
    (κ : ℝ → ℝ) (ρ : ℝ)
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
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      IntegrableOn (fun x : ℝ => ∑' n : ℕ, F n x)
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x ∂volume) =
        ρ / (1 - ρ) := by sorry
