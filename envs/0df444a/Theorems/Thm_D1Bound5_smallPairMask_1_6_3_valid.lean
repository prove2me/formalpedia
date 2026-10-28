-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_6_3_valid
-- name    : D1Bound5.smallPairMask_1_6_3_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:38:31.569804+00:00
-- url     : https://prove2.me/theorems/0a5688ac-27e1-420f-9e37-db7c1ac205a2
-- title:
--   Validity of coordinate square mask smallPairMask_1_6_3
-- statement:
--   The mask `smallPairMask_1_6_3` accepts every square modulo 7 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_6.lean, lines 23-25, SHA-256 a0d4837d188b69add6b5ce02fdb6e201af10251d67a713e6326c08a226549d2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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











theorem _root_.D1Bound5.smallPairMask_1_6_3_valid : CoordinateSquareMaskValid 1 6 6 smallPairMask_1_6_3 := by sorry




































































end D1Bound5
end
