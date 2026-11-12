-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb45_open_C2_compact_hessian_bound
-- name    : AvramDividend.Classical.avram_gb45_open_C2_compact_hessian_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:42:15.250477+00:00
-- url     : https://prove2.me/theorems/09c98534-5951-46ed-824e-867363ca10d5
-- title:
--   Interior C2 regularity gives a compact second-derivative bound
-- statement:
--   Let w be twice continuously differentiable on an open real domain. On any nonempty compact interval contained in that domain, the absolute second iterated derivative of w has a uniform nonnegative real bound. This transfers the open-domain C2 assumption in the original finite-cap verification problem to the bounded Hessian coefficients needed in gb44.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_gb45_open_C2_compact_hessian_bound
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) (a b : ℝ)
    (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, |iteratedDeriv 2 w y| ≤ B := by
  sorry
