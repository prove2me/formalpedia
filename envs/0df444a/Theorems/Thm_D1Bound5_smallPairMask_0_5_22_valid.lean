-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_5_22_valid
-- name    : D1Bound5.smallPairMask_0_5_22_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:38:35.001986+00:00
-- url     : https://prove2.me/theorems/788e66ec-796c-4bd4-a573-5064c4780011
-- title:
--   Validity of coordinate square mask smallPairMask_0_5_22
-- statement:
--   The mask `smallPairMask_0_5_22` accepts every square modulo 83 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 5. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_5.lean, lines 118-120, SHA-256 7a1c66749a7296901da53a817667c58ea7753e9138d50b875e12f2fb9ceb15be. Project: https://github.com/tomislav-math/d1-bound5-lean

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




































































theorem _root_.D1Bound5.smallPairMask_0_5_22_valid : CoordinateSquareMaskValid 0 5 82 smallPairMask_0_5_22 := by sorry











end D1Bound5
end
