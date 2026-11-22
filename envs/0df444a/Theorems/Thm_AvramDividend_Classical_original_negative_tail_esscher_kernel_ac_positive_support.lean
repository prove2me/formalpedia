-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_negative_tail_esscher_kernel_ac_positive_support
-- name    : AvramDividend.Classical.original_negative_tail_esscher_kernel_ac_positive_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:22:14.240993+00:00
-- url     : https://prove2.me/theorems/501256a2-4668-42aa-83c0-ba325d15c317
-- title:
--   Original negative-tail Esscher kernel is positive supported and Lebesgue absolutely continuous
-- statement:
--   For any negative jump measure ν and real Esscher parameter φ, define the exact original tail kernel on t>0 as the restriction to positive t of Lebesgue measure weighted by exp(−φt) times the ENNReal original negative jump tail ν((−∞,−t)). The kernel vanishes on t≤0, is absolutely continuous with respect to Lebesgue measure, and has no point atoms. These properties are the structural input to the finite killed-geometric potential and the derivative/convolution atomlessness argument, independent of finite variation.
-- source:
--   Pinned Mathlib withDensity_absolutelyContinuous, Measure.absolutelyContinuous_restrict, Measure.restrict_apply, singleton volume null; original killed Bernstein Proved 0cb20c38; source renewal 2fa29eaf.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_negative_tail_esscher_kernel_ac_positive_support (ν : Measure ℝ) (φ : ℝ) :
    let κ : Measure ℝ :=
      ((volume : Measure ℝ).withDensity
        (fun t : ℝ =>
          ENNReal.ofReal (Real.exp (-(φ * t))) * ν (Iio (-t)))).restrict
          (Ioi (0 : ℝ))
    κ (Iic (0 : ℝ)) = 0 ∧
    κ ≪ (volume : Measure ℝ) ∧
    (∀ x : ℝ, κ {x} = 0) := by sorry
