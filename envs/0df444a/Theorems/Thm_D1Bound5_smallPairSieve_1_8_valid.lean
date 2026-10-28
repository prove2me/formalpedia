-- Prove2me | Theorems.Thm_D1Bound5_smallPairSieve_1_8_valid
-- name    : D1Bound5.smallPairSieve_1_8_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:09.162444+00:00
-- url     : https://prove2.me/theorems/9c0c24c1-647d-40e2-ae4c-f8c3a3f35648
-- title:
--   Small Pair Sieve 1 8 valid
-- statement:
--   Auxiliary result `smallPairSieve_1_8_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairSieve_1_8.lean, lines 160-187, SHA-256 380989e40c875e6a4f2db650c09a50e5c724b19eff67f6343cbe03358ae7c4b3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_8_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.D1Bound5.smallPairSieve_1_8_valid : CoordinateSquareSieveValid 1 8 smallPairSieve_1_8 := by sorry

end D1Bound5
end
