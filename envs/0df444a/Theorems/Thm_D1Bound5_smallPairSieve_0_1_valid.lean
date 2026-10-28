-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_0_1_valid
-- name    : D1Bound5.smallPairSieve_0_1_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:13.191645+00:00
-- url     : https://prove2.me/theorems/419ca4e8-e847-4760-9ab0-82cf5757a4d4
-- title:
--   Small Pair Sieve 0 1 valid
-- statement:
--   Auxiliary result `smallPairSieve_0_1_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_0_1.lean, lines 160-187, SHA-256 eaf1d5f5326c4a56c61103de3d113bacbce9b50a1751561fda279bb01be33134. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_0_1_valid : CoordinateSquareSieveValid 0 1 smallPairSieve_0_1 := by sorry

end D1Bound5
end
