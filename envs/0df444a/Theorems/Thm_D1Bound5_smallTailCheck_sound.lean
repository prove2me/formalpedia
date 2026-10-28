-- Prove2me | Theorems.Thm_D1Bound5_smallTailCheck_sound
-- name    : D1Bound5.smallTailCheck_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:53.709214+00:00
-- url     : https://prove2.me/theorems/30317766-a8e7-43d8-a250-4fb446392d70
-- title:
--   Small Tail Check sound
-- statement:
--   A checked finite tail excludes every quadruple covered by its norm bounds. This theorem proves the enumeration and edge-coverage implication.
-- source:
--   D1Bound5/FiniteTail.lean, lines 49-75, SHA-256 4a84a3e4ca3b7d43920e93e12f04cbea329f4d21bc5572c8337e09d252793110. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteTail_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions

section
namespace D1Bound5

open QuadInt








theorem _root_.D1Bound5.smallTailCheck_sound {tau nu : ℤ} (hd : 0 < QuadInt.discriminant tau nu)
    (check : SmallTailCheck tau nu) (a b c d : QuadInt tau nu)
    (ha0 : a ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hdb : d ≠ b) (hdc : d ≠ c)
    (hNa : a.norm ≤ b.norm) (hNb : 9 ≤ b.norm)
    (hNbc : b.norm ≤ c.norm) (hNc : c.norm ≤ 15) (hNcd : c.norm ≤ d.norm)
    (hsbc : ∃ r, r*r = b*c+1) (hsab : ∃ r, r*r = a*b+1)
    (hsac : ∃ r, r*r = a*c+1) (hsad : ∃ r, r*r = a*d+1)
    (hreg : regularDefect b c d = 0) : False := by sorry






end D1Bound5
end
