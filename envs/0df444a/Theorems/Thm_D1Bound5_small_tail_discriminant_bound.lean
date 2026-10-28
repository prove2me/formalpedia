-- Prove2me | Theorems.Thm_D1Bound5_small_tail_discriminant_bound
-- name    : D1Bound5.small_tail_discriminant_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:47.197874+00:00
-- url     : https://prove2.me/theorems/d26c83f3-2fcd-4854-9593-c38331169785
-- title:
--   Small tail discriminant bound
-- statement:
--   The small-tail search reduces to Delta<=60 even when both entries are real. In that case their nonreal square root supplies the cutoff.
-- source:
--   D1Bound5/FiniteTail.lean, lines 88-127, SHA-256 4a84a3e4ca3b7d43920e93e12f04cbea329f4d21bc5572c8337e09d252793110. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5

open QuadInt













theorem _root_.D1Bound5.small_tail_discriminant_bound {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) (b c r : QuadInt tau nu)
    (hbc : b ≠ c) (hNb : 9 ≤ b.norm) (hNbc : b.norm ≤ c.norm)
    (hNc : c.norm ≤ 15) (hr : r*r = b*c+1) : QuadInt.discriminant tau nu ≤ 60 := by sorry

end D1Bound5
end
