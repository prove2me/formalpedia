-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_4_19_valid
-- name    : D1Bound5.smallPairMask_1_4_19_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:38:31.348977+00:00
-- url     : https://prove2.me/theorems/5a429ff7-c9d3-40bc-b152-57c5a13b6846
-- title:
--   Validity of coordinate square mask smallPairMask_1_4_19
-- statement:
--   The mask `smallPairMask_1_4_19` accepts every square modulo 71 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 4. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_4.lean, lines 103-105, SHA-256 288ffe9f02afbba2c795f7e67434735805e85f62160458afe593f90ec72631e5. Project: https://github.com/tomislav-math/d1-bound5-lean

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



























































theorem _root_.D1Bound5.smallPairMask_1_4_19_valid : CoordinateSquareMaskValid 1 4 70 smallPairMask_1_4_19 := by sorry




















end D1Bound5
end
