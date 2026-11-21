-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:16:56.142718+00:00
-- url     : https://prove2.me/theorems/f0aa021f-612c-45f5-93b8-049c7dd73041
-- title:
--   Original mixed finite-cap Lévy ruin-overshoot caplinear generator mark Taylor remainder bounded by overshoot
-- statement:
--   Exact finite-cap original spectrally negative Levy ruin-overshoot compensated mark error bound for the corrected caplinear potential V. When premark reserve y exceeds barrier and a negative Lévy mark z crosses below zero, V(y+z)-V(y)-V'(y)z = C.toReal-w(C.toReal)-(y+z). Proved interior C1 gradient secant and nonnegative w(0) imply w(C.toReal)≥C.toReal. Therefore the ruin-crossing mark remainder is ≤ - (postmark reserve), the actual positive overshoot. This is deliberately separate from the proved non-ruin postmark sign ce111444 because the ruined mark remainder can be positive. It supports the original stopped full-mark compensated jump and ruin-contact physical Ito ledger without hiding overshoots or introducing an impossible global slope hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : y + z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y - deriv V y * z ≤ -(y + z) := by sorry
