-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_5_6_valid
-- name    : D1Bound5.smallPairMask_0_5_6_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:41.845674+00:00
-- url     : https://prove2.me/theorems/cfb04046-30bc-4983-8b5f-1811d9e3e163
-- title:
--   Validity of coordinate square mask smallPairMask_0_5_6
-- statement:
--   The mask `smallPairMask_0_5_6` accepts every square modulo 17 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 5. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_5.lean, lines 38-40, SHA-256 7a1c66749a7296901da53a817667c58ea7753e9138d50b875e12f2fb9ceb15be. Project: https://github.com/tomislav-math/d1-bound5-lean

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




















theorem _root_.D1Bound5.smallPairMask_0_5_6_valid : CoordinateSquareMaskValid 0 5 16 smallPairMask_0_5_6 := by sorry



























































end D1Bound5
end
