-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_1_5_18_valid
-- name    : D1Bound5.smallPairMask_1_5_18_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:37:35.690886+00:00
-- url     : https://prove2.me/theorems/fb8b30b6-caa7-4148-84b0-4d8dce25088c
-- title:
--   Validity of coordinate square mask smallPairMask_1_5_18
-- statement:
--   The mask `smallPairMask_1_5_18` accepts every square modulo 67 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 1 and ν = 5. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_1_5.lean, lines 98-100, SHA-256 c3b18f5f92d3bd3049e97d354d5517844eb8013847c09db6dcd9e0cf4f226890. Project: https://github.com/tomislav-math/d1-bound5-lean

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
























































theorem _root_.D1Bound5.smallPairMask_1_5_18_valid : CoordinateSquareMaskValid 1 5 66 smallPairMask_1_5_18 := by sorry























end D1Bound5
end
