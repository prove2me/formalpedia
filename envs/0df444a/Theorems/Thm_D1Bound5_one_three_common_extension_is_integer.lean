-- Prove2me | Theorems.Thm_D1Bound5_one_three_common_extension_is_integer
-- name    : D1Bound5.one_three_common_extension_is_integer
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:32.998786+00:00
-- url     : https://prove2.me/theorems/1d320a6c-35cb-40f3-81ed-016d69257e27
-- title:
--   One three common extension is integer
-- statement:
--   Coordinate-model form of the rationality part of lem:pr-one-three.
-- source:
--   D1Bound5/OneThree.lean, lines 113-123, SHA-256 c460b2250b70545a8f61a27e15dc979839749602cbbccd3fc8fadf6e21e02682. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5









theorem _root_.D1Bound5.one_three_common_extension_is_integer (tau nu : ℤ)
    (hd : 0 < QuadInt.discriminant tau nu) {z : QuadInt tau nu}
    (hr : ∃ r, r*r = z+1) (hs : ∃ s, s*s = 3*z+1) :
    ∃ n : ℤ, z = (n : QuadInt tau nu) := by sorry

end D1Bound5
end
