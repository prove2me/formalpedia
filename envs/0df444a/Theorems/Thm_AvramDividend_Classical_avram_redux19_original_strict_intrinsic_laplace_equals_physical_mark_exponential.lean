-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_intrinsic_laplace_equals_physical_mark_exponential
-- name    : AvramDividend.Classical.avram_redux19_original_strict_intrinsic_laplace_equals_physical_mark_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:08:43.710482+00:00
-- url     : https://prove2.me/theorems/7b62468c-e27e-4be6-bd78-0d0573c71b5b
-- title:
--   Original strict intrinsic Laplace integrand is exactly the physical marked-jump exponential
-- statement:
--   Pointwise on every original spectrally negative Levy sample path, the strict-marked intrinsic jump-measure Laplace exponential equals the real exponential of the sum of physical negative jumps selected on the same strict (0,T] cutoff. This bridges the exact canonical intrinsic stochastic integrand to finite physical marked-jump formulas without surrogate paths or laws.
-- source:
--   Use original strict intrinsic marked finite sum identity, nonnegativity of selected negative jump magnitudes, and the general finite ENNReal-to-real exponential identity. The original physical count and left-limit jump are unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux19_finite_nonnegative_marked_sum_real_exponential
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_strict_intrinsic_laplace_equals_physical_mark_exponential
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
      Real.exp (∑ u ∈ S, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
