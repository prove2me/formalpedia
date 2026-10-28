-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_6_14_valid
-- name    : D1Bound5.smallPairMask_1_6_14_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:38:34.308836+00:00
-- url     : https://prove2.me/theorems/b5d7c6ef-6a8e-45cb-b3c3-e992b6f14f18
-- title:
--   Validity of coordinate square mask smallPairMask_1_6_14
-- statement:
--   The mask `smallPairMask_1_6_14` accepts every square modulo 47 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_6.lean, lines 78-80, SHA-256 a0d4837d188b69add6b5ce02fdb6e201af10251d67a713e6326c08a226549d2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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












































theorem _root_.D1Bound5.smallPairMask_1_6_14_valid : CoordinateSquareMaskValid 1 6 46 smallPairMask_1_6_14 := by sorry



































end D1Bound5
end
