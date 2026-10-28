-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_2_2_valid
-- name    : D1Bound5.smallPairMask_0_2_2_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:40.026896+00:00
-- url     : https://prove2.me/theorems/2b78a9cd-2d28-4cf1-bde9-bee05d7adff5
-- title:
--   Validity of coordinate square mask smallPairMask_0_2_2
-- statement:
--   The mask `smallPairMask_0_2_2` accepts every square modulo 5 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 2. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_2.lean, lines 18-20, SHA-256 727515d7ea212c81f61f9fffb0286c4230effd65a8b39446d16d452557af244b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.smallPairMask_0_2_2_valid : CoordinateSquareMaskValid 0 2 4 smallPairMask_0_2_2 := by sorry







































































end D1Bound5
end
