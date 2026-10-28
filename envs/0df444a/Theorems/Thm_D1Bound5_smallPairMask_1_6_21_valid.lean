-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_6_21_valid
-- name    : D1Bound5.smallPairMask_1_6_21_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:37:27.5674+00:00
-- url     : https://prove2.me/theorems/3222d2b1-55b6-4648-963d-28aabf94498f
-- title:
--   Validity of coordinate square mask smallPairMask_1_6_21
-- statement:
--   The mask `smallPairMask_1_6_21` accepts every square modulo 79 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_6.lean, lines 113-115, SHA-256 a0d4837d188b69add6b5ce02fdb6e201af10251d67a713e6326c08a226549d2d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_6_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

































































theorem _root_.D1Bound5.smallPairMask_1_6_21_valid : CoordinateSquareMaskValid 1 6 78 smallPairMask_1_6_21 := by sorry














end D1Bound5
end
