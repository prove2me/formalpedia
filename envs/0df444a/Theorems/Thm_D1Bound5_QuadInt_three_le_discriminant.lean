-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_three_le_discriminant
-- name    : D1Bound5.QuadInt.three_le_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:29.190945+00:00
-- url     : https://prove2.me/theorems/ddd84ab1-1f80-46ea-8c5c-d1ba9872f7fc
-- title:
--   Quad Int — three le discriminant
-- statement:
--   Every positive discriminant of an integral quadratic coordinate ring is at least three, including nonmaximal orders.
-- source:
--   D1Bound5/OneThree.lean, lines 6-17, SHA-256 c460b2250b70545a8f61a27e15dc979839749602cbbccd3fc8fadf6e21e02682. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.QuadInt.three_le_discriminant {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) :
    3 ≤ QuadInt.discriminant tau nu := by sorry








end D1Bound5
end
