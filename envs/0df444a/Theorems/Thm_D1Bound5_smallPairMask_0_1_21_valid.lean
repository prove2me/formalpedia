-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_1_21_valid
-- name    : D1Bound5.smallPairMask_0_1_21_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:38:29.983962+00:00
-- url     : https://prove2.me/theorems/39828fcd-e92d-46d9-a6db-522570d4c31e
-- title:
--   Validity of coordinate square mask smallPairMask_0_1_21
-- statement:
--   The mask `smallPairMask_0_1_21` accepts every square modulo 79 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 1. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_1.lean, lines 113-115, SHA-256 eaf1d5f5326c4a56c61103de3d113bacbce9b50a1751561fda279bb01be33134. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

































































theorem _root_.D1Bound5.smallPairMask_0_1_21_valid : CoordinateSquareMaskValid 0 1 78 smallPairMask_0_1_21 := by sorry














end D1Bound5
end
