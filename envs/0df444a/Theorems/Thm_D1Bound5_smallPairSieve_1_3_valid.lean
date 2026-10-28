-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_3_valid
-- name    : D1Bound5.smallPairSieve_1_3_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:06.316838+00:00
-- url     : https://prove2.me/theorems/b13c2fc0-89ed-4fd0-ba90-73c63072e1a3
-- title:
--   Small Pair Sieve 1 3 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_3_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_3.lean, lines 160-187, SHA-256 de8037573b1c98178daf87e34451016cb0977dee496699893d9863d236ac805b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_3_valid : CoordinateSquareSieveValid 1 3 smallPairSieve_1_3 := by sorry

end D1Bound5
end
