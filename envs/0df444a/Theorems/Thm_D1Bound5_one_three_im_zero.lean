-- Prove2me | Theorems.Thm_D1Bound5_one_three_im_zero
-- name    : D1Bound5.one_three_im_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:44:56.22696+00:00
-- url     : https://prove2.me/theorems/3019be32-7ed9-43ab-abe8-e0280f4942d8
-- title:
--   One three im zero
-- statement:
--   Every common extension of 1 and 3 has zero imaginary coordinate. This theorem is over the exact quadratic-coordinate model; the global full-ring bridge is not assumed or supplied by this declaration.
-- source:
--   D1Bound5/OneThree.lean, lines 64-111, SHA-256 c460b2250b70545a8f61a27e15dc979839749602cbbccd3fc8fadf6e21e02682. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5







theorem _root_.D1Bound5.one_three_im_zero (tau nu : ℤ)
    (hd : 0 < QuadInt.discriminant tau nu)
    {z r s : QuadInt tau nu} (hr : r*r = z+1) (hs : s*s = 3*z+1) :
    z.im = 0 := by sorry



end D1Bound5
end
