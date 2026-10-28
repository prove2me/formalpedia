-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_untwisted_monotone_series_package
-- name    : AvramDividend.Classical.causal_untwisted_monotone_series_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:18:49.589733+00:00
-- url     : https://prove2.me/theorems/1e37fd54-6b17-4460-bc01-981da6a35677
-- title:
--   Untwist a continuous causal renewal series into monotone convolution powers
-- statement:
--   Given an exponentially tilted causal convolution-power sequence with a continuous summable series, reconstruct its untwisted powers. If the untwisted base kernel is nonnegative and monotone, every power is monotone, and the infinite sum is continuous and monotone on the positive half-line.
-- source:
--   Previously proved exponential convolution factorisation, power continuity, reverse convolution monotonicity and untwisted Neumann series regularity.

import Theorems.Thm_AvramDividend_Classical_causal_exponential_convolution_power_untwist
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_powers_continuity
import Theorems.Thm_AvramDividend_Classical_causal_reverse_Ioc_powers_monotone
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_neumann_series_regular
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_untwisted_monotone_series_package
    (f K : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ : ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hfcont : Continuous f) (hfpos : ∀ x : ℝ, 0 ≤ f x)
    (hfmono : Monotone f)
    (hK : ∀ x : ℝ, K x = Real.exp (-(θ * x)) * f x)
    (hF0 : F 0 = K)
    (hFrec : ∀ n : ℕ, ∀ x : ℝ, F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * F n s ∂volume)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hFsum : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFseriescont : ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici 0)) :
    ∃ U : ℕ → ℝ → ℝ,
      U 0 = f ∧
      (∀ n : ℕ, ∀ x : ℝ, U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ,
        F n x = Real.exp (-(θ * x)) * U n x) ∧
      (∀ n : ℕ, Continuous (U n)) ∧
      (∀ n : ℕ, Monotone (U n)) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => U n x)) ∧
      ContinuousOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) ∧
      MonotoneOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) := by sorry
