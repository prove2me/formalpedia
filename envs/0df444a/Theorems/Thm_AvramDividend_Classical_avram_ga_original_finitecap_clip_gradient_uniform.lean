-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_clip_gradient_uniform
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_clip_gradient_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:00:37.022196+00:00
-- url     : https://prove2.me/theorems/c77a1a12-5332-48ae-b951-91d33fd49df6
-- title:
--   Original finite-cap Gaussian clipping gradient bounded on full interior stopped band
-- statement:
--   The original finite-cap C2 smoothness and strict physical reserve floor delta>0 imply a deterministic uniform absolute bound on deriv w on the compact interior band delta/2 to rational cutoff b<C. Used to bound the first-order source gradient and discount cross errors, without imposing new global smoothness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_clip_gradient_uniform
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      y ∈ Icc a b → |deriv w y| ≤ K := by sorry
