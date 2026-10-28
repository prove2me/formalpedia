-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_Ioc_powers_quadratic
-- name    : AvramDividend.Classical.causal_antitone_Ioc_powers_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:36:17.783748+00:00
-- url     : https://prove2.me/theorems/6ff5cbca-a29e-4a1e-836d-da1c75ff0454
-- title:
--   Quadratic-geometric pointwise bounds for causal positive powers from Ioc mass control
-- statement:
--   A positive continuous antitone L1 causal kernel whose finite-horizon mass is at most rho and whose recursively defined nonnegative convolution powers have geometric Ioc mass control has explicit pointwise power bounds (n+1)^2 rho^(n+1)/x for positive x. This handles the endpoint and convolution-orientation conversions needed by the native Gaussian Neumann construction.
-- source:
--   From the canonically Proved continuous antitone L1 power estimate, establish the missing interface: derive kernel pointwise control from antitonicity and finite-horizon mass, convert the positive Ioc mass bounds to interval-integral bounds, and commute the causal power recursion. This plugs directly into causal_positive_envelope_geometric_powers for the Gaussian Esscher C1 resolvent.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_continuous_antitone_L1_powers_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_antitone_positive_kernel_mass_lower_bound
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_Ioc_powers_quadratic
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hKL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hKmass : ∀ y : ℝ, 0 ≤ y →
      (∫ t in Ioc (0 : ℝ) y, κ t ∂volume) ≤ ρ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ F n t)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFmass : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in Ioc (0 : ℝ) u, F n s ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by sorry
