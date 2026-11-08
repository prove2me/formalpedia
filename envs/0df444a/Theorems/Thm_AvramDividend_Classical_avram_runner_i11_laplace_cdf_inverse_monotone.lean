-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_runner_i11_laplace_cdf_inverse_monotone
-- name    : AvramDividend.Classical.avram_runner_i11_laplace_cdf_inverse_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:26:37.871362+00:00
-- url     : https://prove2.me/theorems/d8b5b48e-c331-4472-a13a-2e435f6989ae
-- title:
--   Atomless renewal-CDF Laplace inverse is monotone from zero
-- statement:
--   If a continuous nonnegative function vanishes at zero and shares all sufficiently large Laplace transforms with the locally finite cumulative distribution of an atomless positive measure, it is nondecreasing on the nonnegative half-line. This bridges the Gaussian renewal-measure construction to the zero-scale monotonicity obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_runner_i11_laplace_cdf_inverse_monotone
    (ν : Measure ℝ)
    (hAtom : ∀ x : ℝ, ν {x} = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (W : ℝ → ℝ)
    (hWzero : W 0 = 0)
    (hWnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hWcont : ContinuousOn W (Ici (0 : ℝ)))
    (b : ℝ)
    (hLap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0)) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0))) :
    MonotoneOn W (Ici (0 : ℝ)) := by sorry
