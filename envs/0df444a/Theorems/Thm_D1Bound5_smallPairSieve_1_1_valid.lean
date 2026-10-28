-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_1_valid
-- name    : D1Bound5.smallPairSieve_1_1_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:20.859282+00:00
-- url     : https://prove2.me/theorems/2e0d8f24-618f-4b7e-af43-987b2da93c48
-- title:
--   Small Pair Sieve 1 1 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_1_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_1.lean, lines 160-187, SHA-256 1d8f95bc4892e90bd05d01e91bc00986257d3ff7687a0c2cb9996f150d2f1c65. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_1_valid : CoordinateSquareSieveValid 1 1 smallPairSieve_1_1 := by sorry

end D1Bound5
end
