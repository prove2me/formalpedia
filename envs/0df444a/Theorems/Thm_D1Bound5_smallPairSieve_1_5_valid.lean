-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_5_valid
-- name    : D1Bound5.smallPairSieve_1_5_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:12.202105+00:00
-- url     : https://prove2.me/theorems/f65fddb4-c68f-42c4-b0c0-2f2a8158420f
-- title:
--   Small Pair Sieve 1 5 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_5_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_5.lean, lines 160-187, SHA-256 c3b18f5f92d3bd3049e97d354d5517844eb8013847c09db6dcd9e0cf4f226890. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_5_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_5_valid : CoordinateSquareSieveValid 1 5 smallPairSieve_1_5 := by sorry

end D1Bound5
end
