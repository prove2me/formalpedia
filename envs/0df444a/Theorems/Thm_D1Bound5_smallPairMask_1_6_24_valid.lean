-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_6_24_valid
-- name    : D1Bound5.smallPairMask_1_6_24_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:29.763984+00:00
-- url     : https://prove2.me/theorems/f62e93d2-4c0d-47f2-aa59-33d8a278b596
-- title:
--   Validity of coordinate square mask smallPairMask_1_6_24
-- statement:
--   The mask `smallPairMask_1_6_24` accepts every square modulo 97 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_6.lean, lines 128-130, SHA-256 a0d4837d188b69add6b5ce02fdb6e201af10251d67a713e6326c08a226549d2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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










































































theorem _root_.D1Bound5.smallPairMask_1_6_24_valid : CoordinateSquareMaskValid 1 6 96 smallPairMask_1_6_24 := by sorry





end D1Bound5
end
