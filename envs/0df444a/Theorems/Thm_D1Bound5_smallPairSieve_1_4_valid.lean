-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_4_valid
-- name    : D1Bound5.smallPairSieve_1_4_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:33.611653+00:00
-- url     : https://prove2.me/theorems/9e0bf594-472a-40c1-aa6c-a3e5f23515cf
-- title:
--   Small Pair Sieve 1 4 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_4_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_4.lean, lines 160-187, SHA-256 288ffe9f02afbba2c795f7e67434735805e85f62160458afe593f90ec72631e5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_4_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_4_valid : CoordinateSquareSieveValid 1 4 smallPairSieve_1_4 := by sorry

end D1Bound5
end
