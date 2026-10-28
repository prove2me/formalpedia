-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_3_4_valid
-- name    : D1Bound5.smallPairMask_1_3_4_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:35:34.901978+00:00
-- url     : https://prove2.me/theorems/363b3aca-fa06-4904-95d4-33a9d9fc1922
-- title:
--   Validity of coordinate square mask smallPairMask_1_3_4
-- statement:
--   The mask `smallPairMask_1_3_4` accepts every square modulo 11 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 3. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_3.lean, lines 28-30, SHA-256 de8037573b1c98178daf87e34451016cb0977dee496699893d9863d236ac805b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














theorem _root_.D1Bound5.smallPairMask_1_3_4_valid : CoordinateSquareMaskValid 1 3 10 smallPairMask_1_3_4 := by sorry

































































end D1Bound5
end
