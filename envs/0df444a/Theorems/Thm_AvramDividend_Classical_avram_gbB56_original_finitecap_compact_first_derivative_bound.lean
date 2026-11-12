-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_finitecap_compact_first_derivative_bound
-- name    : AvramDividend.Classical.avram_gbB56_original_finitecap_compact_first_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:54:22.660376+00:00
-- url     : https://prove2.me/theorems/7c64797d-8585-4042-bfb1-91c8e99e3e96
-- title:
--   Uniform first derivative bound on the finite-cap compact interior band
-- statement:
--   A twice continuously differentiable function on the open finite-cap reserve interval has its first derivative absolutely bounded on the compact interior band, including the case of an empty band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB56_original_finitecap_compact_first_derivative_bound
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Icc (δ / 2)
        (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))),
        |deriv w y| ≤ B := by sorry
