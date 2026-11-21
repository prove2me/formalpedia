-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:14:44.026175+00:00
-- url     : https://prove2.me/theorems/ce111444-ac36-476e-a14d-fca6d7067be9
-- title:
--   Finite-cap original stopped non-ruin Lévy marked jump upper-strip compensated Taylor term is nonpositive from candidate gradient
-- statement:
--   Genuine active-region corrected finite-cap Lévy marked-jump upper-strip compensated Taylor sign. For a premark reserve strictly above finite cap C and a marked postreserve y+z still nonnegative (no ruin crossing), original candidate continuous on [0,infty) with C1 interior derivative ≥1 implies the caplinear extension has nonpositive compensated generator integrand. The full below-cap secant inequality follows from existing Proved avram_p3_bv_finite_cap_linear_crossing_secant, the downcross compensated sign from Proved 38ab18ed, and the purely above-cap zero jump from Proved c82da644. This directly removes the unrealistic global negative-reserve slope hypothesis in earlier 580c3833; marks crossing into negative ruin are deliberately excluded and must be handled by the original stopped ruin-contact ledger. No local Lean checking; remote compile required.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : 0 ≤ y + z) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y - deriv V y * z ≤ 0 := by sorry
