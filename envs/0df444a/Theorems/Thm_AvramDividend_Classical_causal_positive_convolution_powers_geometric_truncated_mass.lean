-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass
-- name    : AvramDividend.Classical.causal_positive_convolution_powers_geometric_truncated_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:08:15.022743+00:00
-- url     : https://prove2.me/theorems/fb78fb76-764d-4300-8328-fc5221cdfcee
-- title:
--   Positive causal convolution powers have geometric truncated mass
-- statement:
--   For a nonnegative positive-time L1 kernel, construct nonnegative causal convolution powers whose integral over every initial interval (0,x] is bounded by the appropriate geometric power of the total kernel mass. Combines exact total-mass recursion, set-integral positivity and domination by full positive-time mass.
-- source:
--   Apply the existing exact L1 convolution-power construction, the Ioc positivity induction and the proved inequality for nonnegative truncated integrals.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_exact_mass_geometric
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_nonnegative
import Theorems.Thm_AvramDividend_Classical_positive_nonnegative_interval_integral_le_global

open MeasureTheory Set

theorem AvramDividend.Classical.causal_positive_convolution_powers_geometric_truncated_mass
    (κ : ℝ → ℝ)
    (hκ : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
        (∫ t in Ioc (0 : ℝ) x, F n t ∂volume) ≤
        (∫ t in Ioi (0 : ℝ), κ t ∂volume) ^ (n + 1)) := by sorry
