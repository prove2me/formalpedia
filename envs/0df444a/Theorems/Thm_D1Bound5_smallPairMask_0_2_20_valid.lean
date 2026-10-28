-- Prove2me | Theorems.Thm_D1Bound5_smallPairMask_0_2_20_valid
-- name    : D1Bound5.smallPairMask_0_2_20_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:25.731353+00:00
-- url     : https://prove2.me/theorems/e38eb0d1-e79b-473e-990a-051e58c021de
-- title:
--   Validity of coordinate square mask smallPairMask_0_2_20
-- statement:
--   The mask `smallPairMask_0_2_20` accepts every square modulo 73 in the quadratic coordinate algebra with relation ω² = τω − ν, where τ = 0 and ν = 2. This includes the zero square.
-- source:
--   D1Bound5/SmallPairSieve_0_2.lean, lines 108-110, SHA-256 727515d7ea212c81f61f9fffb0286c4230effd65a8b39446d16d452557af244b. Project: https://github.com/tomislav-math/d1-bound5-lean

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






























































theorem _root_.D1Bound5.smallPairMask_0_2_20_valid : CoordinateSquareMaskValid 0 2 72 smallPairMask_0_2_20 := by sorry

















end D1Bound5
end
