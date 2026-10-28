-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_8_12_valid
-- name    : D1Bound5.smallPairMask_1_8_12_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:35:32.175283+00:00
-- url     : https://prove2.me/theorems/c72e47f4-9467-48ef-8576-f3cb4d94260c
-- title:
--   Validity of coordinate square mask smallPairMask_1_8_12
-- statement:
--   The mask `smallPairMask_1_8_12` accepts every square modulo 41 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 8. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_8.lean, lines 68-70, SHA-256 380989e40c875e6a4f2db650c09a50e5c724b19eff67f6343cbe03358ae7c4b3. Project: https://github.com/tomislav-math/d1-bound5-lean

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






































theorem _root_.D1Bound5.smallPairMask_1_8_12_valid : CoordinateSquareMaskValid 1 8 40 smallPairMask_1_8_12 := by sorry









































end D1Bound5
end
