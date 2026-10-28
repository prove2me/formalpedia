-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared22_indexed_chunk06_checked
-- name    : D1Bound5.PairGraphPrepared22.indexed_chunk06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:48.303252+00:00
-- url     : https://prove2.me/theorems/94271a0b-118e-4d0a-a844-abb9bfd99a4f
-- title:
--   Indexed mutation-closure certificate for prepared pair 22
-- statement:
--   For prepared pair 22, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure22Chunk06.lean, lines 9-14, SHA-256 e65761b72eef7fbb9ba3ef915d50ea149091dd6c5ac81fc92068916ee55be00c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData22_Definitions_003

section
namespace D1Bound5.PairGraphPrepared22
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared22.indexed_chunk06_checked :
    pairIndexedWitnessesPrefixBool smallPairA_22 smallPairB_22 anchorRoot
      (10^1100) smallPairClosure_22 128
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairGraphPrepared22
end
