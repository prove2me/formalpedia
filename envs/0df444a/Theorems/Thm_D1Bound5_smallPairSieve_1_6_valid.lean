-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_6_valid
-- name    : D1Bound5.smallPairSieve_1_6_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:09.174989+00:00
-- url     : https://prove2.me/theorems/7b09db0c-6522-4908-8564-b0a00290cbfa
-- title:
--   Small Pair Sieve 1 6 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_6_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_6.lean, lines 160-187, SHA-256 a0d4837d188b69add6b5ce02fdb6e201af10251d67a713e6326c08a226549d2d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_6_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_6_valid : CoordinateSquareSieveValid 1 6 smallPairSieve_1_6 := by sorry

end D1Bound5
end
