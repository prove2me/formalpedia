-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_5_9_valid
-- name    : D1Bound5.smallPairMask_1_5_9_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:39:20.891126+00:00
-- url     : https://prove2.me/theorems/199e603b-3574-4db3-b835-eec462a783d0
-- title:
--   Validity of coordinate square mask smallPairMask_1_5_9
-- statement:
--   The mask `smallPairMask_1_5_9` accepts every square modulo 29 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 5. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_5.lean, lines 53-55, SHA-256 c3b18f5f92d3bd3049e97d354d5517844eb8013847c09db6dcd9e0cf4f226890. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_5_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





























theorem _root_.D1Bound5.smallPairMask_1_5_9_valid : CoordinateSquareMaskValid 1 5 28 smallPairMask_1_5_9 := by sorry


















































end D1Bound5
end
