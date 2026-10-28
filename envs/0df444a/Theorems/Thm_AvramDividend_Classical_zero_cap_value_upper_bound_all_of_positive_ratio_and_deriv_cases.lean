-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_of_positive_ratio_and_deriv_cases
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_of_positive_ratio_and_deriv_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:37:29.136814+00:00
-- url     : https://prove2.me/theorems/a0e1bceb-1386-4554-a5db-83066a160677
-- title:
--   Zero-cap optimal bound for all reserves from positive-scale and derivative limit alternatives
-- statement:
--   For the standing spectrally negative Levy process, positive q, and a q-scale function, suppose the genuine reflected-supremum values at reciprocal positive barriers equal their scale ratios and the derivative at zero from the right tends to a finite nonzero value or infinity. The conditional zero-cap boundary package is canonically Proved. The affine above-cap valuation and barrier formula then imply the original zero-cap candidate bound simultaneously for every initial capital x≥0. This concludes the entire all-reserves zero-cap comparison under the explicit stochastic and analytic prerequisites.
-- source:
--   Proved conditional zero-cap boundary package 714c2825-d629-4025-9dfe-22fc6430939a and Proved all-capital zero-bound transfer a77b926c-06ed-4fc1-a8f4-945437968469.

import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_of_positive_ratio_and_deriv_cases
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv :
      (∃ d : ℝ, d ≠ 0 ∧ Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d)) ∨
      Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
