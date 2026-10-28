-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_at_zero
-- name    : AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:28:28.595724+00:00
-- url     : https://prove2.me/theorems/e49c8957-07c7-447b-8e36-226ce9ab65ed
-- title:
--   Subunit Esscher-type causal renewal powers admit an integrable density all the way to zero
-- statement:
--   For a continuous antitone nonnegative causal kernel with strictly subunit positive total mass, construct its recursively defined full-real convolution powers, prove positive-time nonnegativity and quadratic geometric pointwise decay, and crucially prove the summed renewal density is interval-integrable from zero. This combines the existing renewal-power existence theorem with newly verified support, exact mass, pointwise convergence and Tonelli integrability results. It isolates the entire deterministic zero-endpoint analytic portion needed by the open bounded-variation Esscher scale identification.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_interval_integrable_at_zero

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_at_zero
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
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x) := by sorry
