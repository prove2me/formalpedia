-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_2_13_valid
-- name    : D1Bound5.smallPairMask_1_2_13_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:41.299557+00:00
-- url     : https://prove2.me/theorems/6ced7f14-0cd8-44fd-8336-bedda042b5b9
-- title:
--   Validity of coordinate square mask smallPairMask_1_2_13
-- statement:
--   The mask `smallPairMask_1_2_13` accepts every square modulo 43 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 2. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_2.lean, lines 73-75, SHA-256 0e06eb108afce10f63dd87b8402973d477820e1a7d76cfa29f8e0be3d77d5235. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0









































theorem _root_.D1Bound5.smallPairMask_1_2_13_valid : CoordinateSquareMaskValid 1 2 42 smallPairMask_1_2_13 := by sorry






































end D1Bound5
end
