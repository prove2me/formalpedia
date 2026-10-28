-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_4_17_valid
-- name    : D1Bound5.smallPairMask_1_4_17_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:45.18899+00:00
-- url     : https://prove2.me/theorems/f3a496bf-bd7a-4b97-b86b-28bfc2bee532
-- title:
--   Validity of coordinate square mask smallPairMask_1_4_17
-- statement:
--   The mask `smallPairMask_1_4_17` accepts every square modulo 61 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 4. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_4.lean, lines 93-95, SHA-256 288ffe9f02afbba2c795f7e67434735805e85f62160458afe593f90ec72631e5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_4_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





















































theorem _root_.D1Bound5.smallPairMask_1_4_17_valid : CoordinateSquareMaskValid 1 4 60 smallPairMask_1_4_17 := by sorry


























end D1Bound5
end
