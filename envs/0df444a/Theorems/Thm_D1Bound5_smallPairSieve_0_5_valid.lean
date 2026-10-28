-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_0_5_valid
-- name    : D1Bound5.smallPairSieve_0_5_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:07.079808+00:00
-- url     : https://prove2.me/theorems/bdf579cf-628a-44ad-90d0-6d624ba41821
-- title:
--   Small Pair Sieve 0 5 valid
-- statement:
--   Auxiliary result `smallPairSieve_0_5_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_0_5.lean, lines 160-187, SHA-256 7a1c66749a7296901da53a817667c58ea7753e9138d50b875e12f2fb9ceb15be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_5_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_0_5_valid : CoordinateSquareSieveValid 0 5 smallPairSieve_0_5 := by sorry

end D1Bound5
end
