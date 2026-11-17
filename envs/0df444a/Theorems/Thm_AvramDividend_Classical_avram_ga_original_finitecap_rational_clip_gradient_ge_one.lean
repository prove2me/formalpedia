-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_rational_clip_gradient_ge_one
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_rational_clip_gradient_ge_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:04:29.191764+00:00
-- url     : https://prove2.me/theorems/4962dd7c-2696-4ce9-9b7c-206c3ac7d5b3
-- title:
--   Original finite-cap clipped corner derivative at b is at least one
-- statement:
--   The original value function gradient inequality 1≤deriv w on (0,C) applies at the strictly interior rational capline corner b=C.toReal*(j+1)/(j+2), using Proved B41. Thus the caplinear function changes slope downward (or remains equal), which is essential for discarding its signed negative local-time contribution in Gaussian Itô-Tanaka estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_rational_clip_gradient_ge_one
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    1 ≤ deriv w b := by sorry
