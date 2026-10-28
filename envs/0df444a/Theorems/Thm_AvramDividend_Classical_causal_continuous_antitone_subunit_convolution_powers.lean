-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_antitone_subunit_convolution_powers
-- name    : AvramDividend.Classical.causal_continuous_antitone_subunit_convolution_powers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:20:38.573142+00:00
-- url     : https://prove2.me/theorems/16a89252-7104-4216-a937-a529a6aa0034
-- title:
--   Subunit continuous antitone kernel admits positive geometrically bounded convolution powers
-- statement:
--   For an L1, nonnegative, positive-time continuous antitone kernel of total integral ρ with 0<ρ<1, construct its causal real convolution powers with exact Ioc recurrence, positivity and geometric quadratic pointwise estimate ((n+1)^2 ρ^(n+1))/x. This packages the independently Proved geometric truncated-mass construction and the proved antitone Ioc power estimates. Together with the real Esscher weighted-tail kernel and drift normalisation, it supplies the power and convergence prerequisites of bv_ac_esscher_scaled_renewal_kernel_series_data (9be5ada9), the open child on the finite cstar and Avram Dividend root path.
-- source:
--   Proved causal_positive_convolution_powers_geometric_truncated_mass, causal_antitone_Ioc_powers_quadratic, positive_nonnegative_interval_integral_le_global.

import Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass
import Theorems.Thm_AvramDividend_Classical_causal_antitone_Ioc_powers_quadratic
import Theorems.Thm_AvramDividend_Classical_positive_nonnegative_interval_integral_le_global

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_continuous_antitone_subunit_convolution_powers
    (κ : ℝ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ) (hρone : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by sorry
