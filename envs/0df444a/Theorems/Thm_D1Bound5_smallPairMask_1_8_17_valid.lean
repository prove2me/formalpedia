-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_8_17_valid
-- name    : D1Bound5.smallPairMask_1_8_17_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:38:24.135037+00:00
-- url     : https://prove2.me/theorems/d9be8487-64f5-4ce0-b8d5-d0e6a34d4b88
-- title:
--   Validity of coordinate square mask smallPairMask_1_8_17
-- statement:
--   The mask `smallPairMask_1_8_17` accepts every square modulo 61 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 8. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_8.lean, lines 93-95, SHA-256 380989e40c875e6a4f2db650c09a50e5c724b19eff67f6343cbe03358ae7c4b3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_8_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





















































theorem _root_.D1Bound5.smallPairMask_1_8_17_valid : CoordinateSquareMaskValid 1 8 60 smallPairMask_1_8_17 := by sorry


























end D1Bound5
end
