-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_5_23_valid
-- name    : D1Bound5.smallPairMask_0_5_23_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:37:30.915864+00:00
-- url     : https://prove2.me/theorems/cfdd0f5b-6a23-4b66-816f-f3659336f966
-- title:
--   Validity of coordinate square mask smallPairMask_0_5_23
-- statement:
--   The mask `smallPairMask_0_5_23` accepts every square modulo 89 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 5. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_5.lean, lines 123-125, SHA-256 7a1c66749a7296901da53a817667c58ea7753e9138d50b875e12f2fb9ceb15be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_5_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







































































theorem _root_.D1Bound5.smallPairMask_0_5_23_valid : CoordinateSquareMaskValid 0 5 88 smallPairMask_0_5_23 := by sorry








end D1Bound5
end
