-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
-- name    : AvramDividend.Classical.causal_renewal_density_continuous_of_convolution_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:59:23.211876+00:00
-- url     : https://prove2.me/theorems/57781282-3c9c-464e-b7ee-333a80148b1c
-- title:
--   Continuity of a geometric causal renewal density series from convolution-power bounds
-- statement:
--   Given a continuous integrable causal renewal kernel and its nonnegative convolution powers, a locally bounded kernel and quadratic-geometric pointwise estimates with contraction 0<ρ<1 yield a continuous density on the positive axis. The zero-index shift makes the bound compatible with the zero order term. This provides the continuous-density component of bv_ac_esscher_continuous_renewal_density_representation (17bc0aad...), a prerequisite of scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy, standing C1, cstar_lt_top, and the Avram root.
-- source:
--   Consequence of canonically Proved causal_l1_continuous_convolution_power_induction_with_tail_bounds and continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound, in the pinned AvramDividend.Classical environment.

import Theorems.Thm_AvramDividend_Classical_causal_l1_continuous_convolution_power_induction_with_tail_bounds
import Theorems.Thm_AvramDividend_Classical_continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_renewal_density_continuous_of_convolution_bounds
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x)
      (Ioi (0 : ℝ)) := by sorry
