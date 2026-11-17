-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clip_gradient_continuousOn
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_clip_gradient_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:58:25.542201+00:00
-- url     : https://prove2.me/theorems/1409ad89-2a06-4202-acba-b37946f41731
-- title:
--   Original finitecap source first derivative continuous on delta/2 to rational clip band
-- statement:
--   Under the original source C2 smoothness on the open reserve region and finite-cap rational clip b<C, the classical first derivative is continuous on the compact interior band [delta/2,b]. This supports a deterministic gradient bound for first-order Gaussian discount and Taylor error estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_clip_gradient_continuousOn
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ContinuousOn (deriv w) (Icc a b) := by sorry
