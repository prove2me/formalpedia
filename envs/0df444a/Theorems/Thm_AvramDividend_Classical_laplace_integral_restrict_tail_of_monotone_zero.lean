-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_integral_restrict_tail_of_monotone_zero
-- name    : AvramDividend.Classical.laplace_integral_restrict_tail_of_monotone_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T06:39:53.949532+00:00
-- url     : https://prove2.me/theorems/c21946b8-1880-47f3-852c-1aa4a28b6395
-- title:
--   A monotone nonnegative scale function vanishing at a has no Laplace mass below a
-- statement:
--   A nonnegative nondecreasing W on the nonnegative real axis which is zero at a>0 must vanish on (0,a]. Consequently its Laplace integral on (0,∞) is equal to its integral on the tail (a,∞) for every real Laplace parameter, with no integrability premise.
-- source:
--   Deterministic set-integral restriction step for the unbounded-variation strict-positivity contradiction in Avram Dividend.

import Mathlib
open MeasureTheory Set Filter

namespace AvramDividend.Classical

theorem laplace_integral_restrict_tail_of_monotone_zero
    (W : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Ici 0))
    (hWa : W a = 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * W x) =
      ∫ x in Ioi a, Real.exp (-β * x) * W x := by
  sorry

end AvramDividend.Classical
