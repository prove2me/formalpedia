-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_2_21_valid
-- name    : D1Bound5.smallPairMask_1_2_21_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:25.125042+00:00
-- url     : https://prove2.me/theorems/ba38bacb-ef6b-401c-bb1e-6408f4c2e69e
-- title:
--   Validity of coordinate square mask smallPairMask_1_2_21
-- statement:
--   The mask `smallPairMask_1_2_21` accepts every square modulo 79 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 2. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_2.lean, lines 113-115, SHA-256 0e06eb108afce10f63dd87b8402973d477820e1a7d76cfa29f8e0be3d77d5235. Project: https://github.com/tomislav-math/d1-bound5-lean

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

































































theorem _root_.D1Bound5.smallPairMask_1_2_21_valid : CoordinateSquareMaskValid 1 2 78 smallPairMask_1_2_21 := by sorry














end D1Bound5
end
