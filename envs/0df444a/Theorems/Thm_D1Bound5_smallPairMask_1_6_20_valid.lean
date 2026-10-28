-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_6_20_valid
-- name    : D1Bound5.smallPairMask_1_6_20_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:32.683192+00:00
-- url     : https://prove2.me/theorems/6eb6cf32-4b13-4ab6-8563-72bf634107c3
-- title:
--   Validity of coordinate square mask smallPairMask_1_6_20
-- statement:
--   The mask `smallPairMask_1_6_20` accepts every square modulo 73 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_6.lean, lines 108-110, SHA-256 a0d4837d188b69add6b5ce02fdb6e201af10251d67a713e6326c08a226549d2d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_6_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0






























































theorem _root_.D1Bound5.smallPairMask_1_6_20_valid : CoordinateSquareMaskValid 1 6 72 smallPairMask_1_6_20 := by sorry

















end D1Bound5
end
