-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_total_mass_resolvent
-- name    : AvramDividend.Classical.causal_subunit_renewal_density_total_mass_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:44:00.554687+00:00
-- url     : https://prove2.me/theorems/334f825c-8320-418b-a623-24260d8cd875
-- title:
--   Constructed causal subunit renewal density has total mass rho over one minus rho
-- statement:
--   Under continuous antitone causal subunit kernel hypotheses, construct full-real convolution powers and establish that their summed positive-time renewal density has total Lebesgue integral rho/(1-rho). The proof connects geometric convolution-power mass, causal support, nonnegative integral/sum interchange and the geometric resolvent identity. It is a directly importable normalisation theorem for the open bounded-variation Esscher renewal scale identification.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
import Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_total_mass_sum
import Mathlib.Analysis.SpecificLimits.Basic

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_renewal_density_total_mass_resolvent
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
      (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x ∂volume) =
        ρ / (1 - ρ) := by sorry
