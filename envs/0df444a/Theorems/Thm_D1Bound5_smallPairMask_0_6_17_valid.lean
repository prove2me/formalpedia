-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_6_17_valid
-- name    : D1Bound5.smallPairMask_0_6_17_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:37:39.507877+00:00
-- url     : https://prove2.me/theorems/b9107006-5a12-4535-82d2-2bce3fe89644
-- title:
--   Validity of coordinate square mask smallPairMask_0_6_17
-- statement:
--   The mask `smallPairMask_0_6_17` accepts every square modulo 61 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_6.lean, lines 93-95, SHA-256 039d6ed0595df155d20a4352a6e96fcb683b909e3c29c990bf40514bd1a3371d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_6_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





















































theorem _root_.D1Bound5.smallPairMask_0_6_17_valid : CoordinateSquareMaskValid 0 6 60 smallPairMask_0_6_17 := by sorry


























end D1Bound5
end
