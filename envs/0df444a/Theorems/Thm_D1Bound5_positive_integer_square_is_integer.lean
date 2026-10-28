-- Prove2me | Theorems.Thm_D1Bound5_positive_integer_square_is_integer
-- name    : D1Bound5.positive_integer_square_is_integer
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:40:03.489993+00:00
-- url     : https://prove2.me/theorems/b7876cf6-2d00-44d8-a7b7-fab679a6f874
-- title:
--   Positive integer square is integer
-- statement:
--   A positive rational integer that is a square in an imaginary quadratic integer ring is already an ordinary integer square.
-- source:
--   D1Bound5/RationalSquares.lean, lines 86-97, SHA-256 4cd56ab129029a6551801f8c22878c2598ef5298b732a909ebb1ad48e70f5e58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5

open QuadInt










theorem _root_.D1Bound5.positive_integer_square_is_integer {tau nu m : ℤ}
    (hd : 0 < discriminant tau nu) (hm : 0 < m)
    (hr : ∃ r : QuadInt tau nu, r*r = (m : QuadInt tau nu)) :
    ∃ n : ℤ, m = n^2 := by sorry

end D1Bound5
end
