-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density
-- name    : AvramDividend.Classical.avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:46:01.90365+00:00
-- url     : https://prove2.me/theorems/d9187db3-1b33-4b09-8063-32bf9f6954b8
-- title:
--   The genuine Esscher scale-CDF law plus a continuous local density gives positive-axis C1 of the q-scale function
-- statement:
--   A source-specific analytic alternative to the reflected-excursion method. Suppose the genuine all-real positive-root Esscher cumulative law equals m exp(-phi x) W(x) on positive capital and has a locally interval-integrable continuous density f on (0,infinity), represented by the cumulative interval integral from any positive anchor a. Then W is continuously differentiable on (0,infinity). The representation is a substantive extra potential-density hypothesis, not a conclusion inferred from CDF monotonicity or absence of atoms. This theorem gives the exact mathematical interface left to derive from genuine Levy fluctuation laws.
-- source:
--   Fundamental theorem of calculus for locally integrable continuous density; Mathlib intervalIntegral.integral_hasDerivAt_right and contDiffOn_one_iff_derivWithin; Proved all-real Esscher CDF scale identity motivates hCDF but does not by itself supply hDensity.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density
    (ν : Measure ℝ) (W : ℝ → ℝ) (φ m a : ℝ)
    (hm : 0 < m) (ha : 0 < a)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume a x)
    (hCDF : ∀ x : ℝ, 0 < x →
      W x = (Real.exp (φ * x) / m) * (ν (Iic x)).toReal)
    (hDensity : ∀ x : ℝ, 0 < x →
      (ν (Iic x)).toReal =
        (ν (Iic a)).toReal + ∫ t in a..x, f t) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
