-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_6_9_valid
-- name    : D1Bound5.smallPairMask_0_6_9_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:29.743993+00:00
-- url     : https://prove2.me/theorems/a102e5a9-8b67-47fc-a330-29966bdfad52
-- title:
--   Validity of coordinate square mask smallPairMask_0_6_9
-- statement:
--   The mask `smallPairMask_0_6_9` accepts every square modulo 29 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 6. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_6.lean, lines 53-55, SHA-256 039d6ed0595df155d20a4352a6e96fcb683b909e3c29c990bf40514bd1a3371d. Project: https://github.com/tomislav-math/d1-bound5-lean

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





























theorem _root_.D1Bound5.smallPairMask_0_6_9_valid : CoordinateSquareMaskValid 0 6 28 smallPairMask_0_6_9 := by sorry


















































end D1Bound5
end
