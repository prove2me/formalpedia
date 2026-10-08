-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_two
-- name    : AvramDividend.Classical.deriv_bounded_on_compact_of_contDiff_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:22:59.308995+00:00
-- url     : https://prove2.me/theorems/686484d4-f35d-4581-b765-3c73c646cfa1
-- title:
--   A C2 function has bounded first derivative on a compact subinterval
-- statement:
--   Suppose a real function W is C2 on (0,a). On any closed interval [l,u] with l<u and [l,u] contained in (0,a), the first derivative is bounded in absolute value by a finite nonnegative constant. Restrict C2 regularity to the compact interval, use continuity of the first iterated derivative there and the extreme-value theorem, and identify the within-derivative with the ordinary derivative because every point of the closed interval is interior to the ambient smoothness domain. This supplies a uniform far-jump compensation bound when integrating a Levy generator over a compact range of starting states.
-- source:
--   Elementary extreme-value theorem and continuous differentiability; auxiliary calculus step for the uniform Levy generator domination in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib

open MeasureTheory Set

namespace AvramDividend.Classical

theorem deriv_bounded_on_compact_of_contDiff_two
    (W : ℝ → ℝ) (a l u : ℝ)
    (hlu : l < u) (hsub : Icc l u ⊆ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l u, |deriv W x| ≤ C := by sorry

end AvramDividend.Classical
