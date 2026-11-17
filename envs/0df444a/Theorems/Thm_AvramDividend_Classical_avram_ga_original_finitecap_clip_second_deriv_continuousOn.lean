-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clip_second_deriv_continuousOn
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_clip_second_deriv_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:54:04.626879+00:00
-- url     : https://prove2.me/theorems/0a078c94-98e7-429a-8171-81030a3c0654
-- title:
--   Original finite cap cutoff admits continuous second derivative on delta/2 to b compact band
-- statement:
--   Given the original finite cap and C2 smoothness on the open interval (0,C), the second classical derivative is continuous on the closed band from delta/2 to b=C.toReal*(j+1)/(j+2). Use proved B41 rational cutoff strictly below C. Empty intervals when delta/2>b are allowed and need no additional assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_clip_second_deriv_continuousOn
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b) := by sorry
