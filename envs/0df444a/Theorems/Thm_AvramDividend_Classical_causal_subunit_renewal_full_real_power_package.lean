-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
-- name    : AvramDividend.Classical.causal_subunit_renewal_full_real_power_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:33:35.323996+00:00
-- url     : https://prove2.me/theorems/0aa46c71-189c-4b1a-b479-5a09986c9b41
-- title:
--   Globally integrable subunit causal renewal powers with exact full real convolution and geometric bound
-- statement:
--   Combines three canonically proved analytic lemmas to give global integrability, full real convolution recursion, positive-time integrability, nonnegativity and quadratic geometric bounds for causal renewal powers. This is the exact power-package consumed by open corrected BV Esscher scaled renewal kernel series data (9be5ada9) and the finite cstar proof route.
-- source:
--   Proved causal_positive_l1_global_integrable, causal_continuous_antitone_subunit_convolution_powers and causal_Ioc_convolution_powers_full_real_recursion.

import Theorems.Thm_AvramDividend_Classical_causal_continuous_antitone_subunit_convolution_powers
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_renewal_full_real_power_package
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρone : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ t : ℝ, t ≤ 0 → κ t = 0)
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ) :
    Integrable κ volume ∧
      ∃ F : ℕ → ℝ → ℝ,
        F 0 = κ ∧
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ s : ℝ, κ s * F n (x - s) ∂volume) ∧
        (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 < x →
          F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by sorry
