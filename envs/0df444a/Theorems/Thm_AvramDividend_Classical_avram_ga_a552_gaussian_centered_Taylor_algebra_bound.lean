-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a552_gaussian_centered_Taylor_algebra_bound
-- name    : AvramDividend.Classical.avram_ga_a552_gaussian_centered_Taylor_algebra_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:58:41.18528+00:00
-- url     : https://prove2.me/theorems/220d3cec-02f9-4b01-90b1-f77f9f55e319
-- title:
--   Bound a discounted centred Gaussian Taylor polynomial by an integrable squared increment
-- statement:
--   For a discount e between zero and one and bounded first and second derivative coefficients, the absolute linear-plus-centred-quadratic Taylor polynomial is bounded by a fixed constant times one plus z squared.
-- source:
--   Triangle inequality, abs z ≤ 1+z², and absolute coefficient bounds

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_a552_gaussian_centered_Taylor_algebra_bound
    (a b z e K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (ha : |a| ≤ K) (hb : |b| ≤ K)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |e * (a * z + (b / 2) * (z ^ 2 - δ))| ≤
      (K * (2 + δ)) * (1 + z ^ 2) := by sorry
