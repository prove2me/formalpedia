-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_repaired_boundary_nonneg_all_cap
-- name    : AvramDividend.Classical.avram_wave3_04_repaired_boundary_nonneg_all_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:48:50.460051+00:00
-- url     : https://prove2.me/theorems/e3cd85ca-9e16-4b4c-8cee-e6de9dc7f20c
-- title:
--   Repaired verification boundary hypothesis implies candidate positivity throughout every cap
-- statement:
--   The source paper's missing boundary premise w(0)≥0, combined with the gradient verification inequality w'≥1 and C1 regularity in the positive interior and continuity at zero, forces w(y)≥0 for every nonnegative reserve y whose ENNReal image does not exceed the cap. The argument includes cap endpoints and the zero-cap case. For positive cap the existing Proved full-cap gradient secant with a=0 gives w(y)−w(0)≥y≥0; at cap zero the reserve must be zero.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), requires w(0)≥0. Canonical Proved cap gradient secant 2ba5cc4f-3aab-40ea-a59a-8a49633c7595. Exact pinned remote candidate probe 4131b5b5-462c-4786-a9bd-25e2d62b3d7b reached sentinel, candidate SHA-256 c89d9982d6334d21f494f250363777742ff5a4d2282407e41d15a15f8445abcd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_repaired_boundary_nonneg_all_cap
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y)
    (hcap : ENNReal.ofReal y ≤ C) :
    0 ≤ w y := by sorry
