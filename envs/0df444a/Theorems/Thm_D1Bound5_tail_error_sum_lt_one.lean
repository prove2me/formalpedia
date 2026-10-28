-- Prove2me | Theorems.Thm_D1Bound5_tail_error_sum_lt_one
-- name    : D1Bound5.tail_error_sum_lt_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:35:51.396979+00:00
-- url     : https://prove2.me/theorems/641f36b9-b791-4aad-8bf6-4260d6706531
-- title:
--   Tail error sum lt one
-- statement:
--   The real error estimate needed for a regular tail with C>=4. The variables x,y,z are the moduli of square roots of a,b,c.
-- source:
--   D1Bound5/TailErrorBounds.lean, lines 7-67, SHA-256 4bc1a1931cb13e58318d9d21cfd92884eddf3b1600951c14e0b1db708cae4598. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.tail_error_sum_lt_one (x y z er eu ev ew : ℝ)
    (hx : 1 ≤ x) (hy : (12/7 : ℝ) ≤ y) (hz : 2 ≤ z) (hxy : x ≤ y)
    (her : 0 ≤ er) (heu : 0 ≤ eu) (hev : 0 ≤ ev) (_hew : 0 ≤ ew)
    (hr : (39/20 : ℝ)*y*z*er < 1)
    (hu : (9/5 : ℝ)*x*y*eu < 1)
    (hv : (13/7 : ℝ)*x*z*ev < 1)
    (hw : (216/125 : ℝ)*x*z*ew < 1+2*x^2*er) : eu+ev+ew < 1 := by sorry



end D1Bound5
end
