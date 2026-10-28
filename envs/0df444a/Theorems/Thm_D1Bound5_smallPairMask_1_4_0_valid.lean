-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_4_0_valid
-- name    : D1Bound5.smallPairMask_1_4_0_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:40.643993+00:00
-- url     : https://prove2.me/theorems/f39140d6-12e4-4311-8943-a4687997750d
-- title:
--   Validity of coordinate square mask smallPairMask_1_4_0
-- statement:
--   The mask `smallPairMask_1_4_0` accepts every square modulo 2 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 4. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_4.lean, lines 8-10, SHA-256 288ffe9f02afbba2c795f7e67434735805e85f62160458afe593f90ec72631e5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.smallPairMask_1_4_0_valid : CoordinateSquareMaskValid 1 4 1 smallPairMask_1_4_0 := by sorry













































































end D1Bound5
end
