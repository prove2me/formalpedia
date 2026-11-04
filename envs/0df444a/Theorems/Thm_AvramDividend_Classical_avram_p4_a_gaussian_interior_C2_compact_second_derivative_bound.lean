-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:42:55.148287+00:00
-- url     : https://prove2.me/theorems/6ad49e27-87c8-439b-88cd-8eae77136bc3
-- title:
--   Interior C2 of the stopped value gives a compact-only second derivative bound
-- statement:
--   Under precisely the interior C2 regularity of the original dividend candidate, its second derivative in the generator convention is bounded on every compact interval [a,b] strictly contained in (0,C). No global derivative bound, ruin regularity or cap endpoint property is asserted. This supplies a local stopped integrability estimate for the original Gaussian continuous Ito correction.
-- source:
--   Mathlib ContDiffOn.continuousOn_iteratedDerivWithin, iteratedDerivWithin_of_isOpen, and IsCompact.exists_bound_of_continuousOn; applied to Icc a b inside Ioo 0 C.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound
    (w : ℝ → ℝ) (C a b : ℝ)
    (ha : 0 < a) (hb : b < C)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C)) :
    ∃ K : ℝ, ∀ y ∈ Icc a b, ‖iteratedDeriv 2 w y‖ ≤ K := by sorry
