-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_0_2_valid
-- name    : D1Bound5.smallPairSieve_0_2_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:09.680418+00:00
-- url     : https://prove2.me/theorems/6409cd28-d736-4135-9fb7-257d7b94fb58
-- title:
--   Small Pair Sieve 0 2 valid
-- statement:
--   Auxiliary result `smallPairSieve_0_2_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_0_2.lean, lines 160-187, SHA-256 727515d7ea212c81f61f9fffb0286c4230effd65a8b39446d16d452557af244b. Project: https://github.com/tomislav-math/d1-bound5-lean

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














































































theorem _root_.D1Bound5.smallPairSieve_0_2_valid : CoordinateSquareSieveValid 0 2 smallPairSieve_0_2 := by sorry

end D1Bound5
end
