-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_2_valid
-- name    : D1Bound5.smallPairSieve_1_2_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:27.476933+00:00
-- url     : https://prove2.me/theorems/7b021dfb-4e96-44aa-b9e3-d1fbd75b332f
-- title:
--   Small Pair Sieve 1 2 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_2_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_2.lean, lines 160-187, SHA-256 0e06eb108afce10f63dd87b8402973d477820e1a7d76cfa29f8e0be3d77d5235. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_2_valid : CoordinateSquareSieveValid 1 2 smallPairSieve_1_2 := by sorry

end D1Bound5
end
