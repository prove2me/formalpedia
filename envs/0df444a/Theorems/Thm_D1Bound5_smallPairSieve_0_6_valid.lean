-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_0_6_valid
-- name    : D1Bound5.smallPairSieve_0_6_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:08.998981+00:00
-- url     : https://prove2.me/theorems/707d5832-f809-43a0-bf88-e0f45ea53756
-- title:
--   Small Pair Sieve 0 6 valid
-- statement:
--   Auxiliary result `smallPairSieve_0_6_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_0_6.lean, lines 160-187, SHA-256 039d6ed0595df155d20a4352a6e96fcb683b909e3c29c990bf40514bd1a3371d. Project: https://github.com/tomislav-math/d1-bound5-lean

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














































































theorem _root_.D1Bound5.smallPairSieve_0_6_valid : CoordinateSquareSieveValid 0 6 smallPairSieve_0_6 := by sorry

end D1Bound5
end
