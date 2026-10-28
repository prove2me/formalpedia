-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_2_2_valid
-- name    : D1Bound5.smallPairMask_1_2_2_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:35:50.34539+00:00
-- url     : https://prove2.me/theorems/145387e1-7c85-433a-9041-8a8d6df7f16f
-- title:
--   Validity of coordinate square mask smallPairMask_1_2_2
-- statement:
--   The mask `smallPairMask_1_2_2` accepts every square modulo 5 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 2. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_2.lean, lines 18-20, SHA-256 0e06eb108afce10f63dd87b8402973d477820e1a7d76cfa29f8e0be3d77d5235. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.smallPairMask_1_2_2_valid : CoordinateSquareMaskValid 1 2 4 smallPairMask_1_2_2 := by sorry







































































end D1Bound5
end
