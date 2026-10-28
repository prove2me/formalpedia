-- Prove2me | Theorems.Thm_D1Bound5_tail_sum_root_bounds
-- name    : D1Bound5.tail_sum_root_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:42:03.0705+00:00
-- url     : https://prove2.me/theorems/51a40f1e-6bd6-473e-b0fe-170ad07071c9
-- title:
--   Tail sum root bounds
-- statement:
--   The tail perturbation also bounds the modulus of beta+gamma away from zero, and leaves enough room for a second square-root perturbation.
-- source:
--   D1Bound5/TailErrorBounds.lean, lines 69-89, SHA-256 4bc1a1931cb13e58318d9d21cfd92884eddf3b1600951c14e0b1db708cae4598. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.tail_sum_root_bounds (x y z p er : ℝ)
    (hx : 1 ≤ x) (hy : (12/7 : ℝ) ≤ y) (hz : 2 ≤ z)
    (hp : 0 ≤ p) (her : 0 ≤ er) (hr : (39/20 : ℝ)*y*z*er < 1)
    (horder : z^2 ≤ p^2+2*er) :
    (24/25 : ℝ)*z < p ∧ 1+2*x^2*er < (9/25 : ℝ)*(x*p)^2 := by sorry

end D1Bound5
end
