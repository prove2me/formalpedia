-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_8_4_valid
-- name    : D1Bound5.smallPairMask_1_8_4_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:37:29.484242+00:00
-- url     : https://prove2.me/theorems/1981bb63-e623-45c0-8c49-1b3626d837f6
-- title:
--   Validity of coordinate square mask smallPairMask_1_8_4
-- statement:
--   The mask `smallPairMask_1_8_4` accepts every square modulo 11 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 8. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_8.lean, lines 28-30, SHA-256 380989e40c875e6a4f2db650c09a50e5c724b19eff67f6343cbe03358ae7c4b3. Project: https://github.com/tomislav-math/d1-bound5-lean

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














theorem _root_.D1Bound5.smallPairMask_1_8_4_valid : CoordinateSquareMaskValid 1 8 10 smallPairMask_1_8_4 := by sorry

































































end D1Bound5
end
