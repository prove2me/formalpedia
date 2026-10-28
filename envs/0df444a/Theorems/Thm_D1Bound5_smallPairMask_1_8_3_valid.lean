-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_8_3_valid
-- name    : D1Bound5.smallPairMask_1_8_3_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:35:36.82739+00:00
-- url     : https://prove2.me/theorems/941c1a92-dc0a-4b0b-89ce-4dc376624353
-- title:
--   Validity of coordinate square mask smallPairMask_1_8_3
-- statement:
--   The mask `smallPairMask_1_8_3` accepts every square modulo 7 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 8. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_8.lean, lines 23-25, SHA-256 380989e40c875e6a4f2db650c09a50e5c724b19eff67f6343cbe03358ae7c4b3. Project: https://github.com/tomislav-math/d1-bound5-lean

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











theorem _root_.D1Bound5.smallPairMask_1_8_3_valid : CoordinateSquareMaskValid 1 8 6 smallPairMask_1_8_3 := by sorry




































































end D1Bound5
end
