-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared22_indexed_chunk00_checked
-- name    : D1Bound5.PairGraphPrepared22.indexed_chunk00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:35.108953+00:00
-- url     : https://prove2.me/theorems/023458ee-0f8a-4887-b76a-71a2273fe567
-- title:
--   Indexed mutation-closure certificate for prepared pair 22
-- statement:
--   For prepared pair 22, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure22Chunk00.lean, lines 9-14, SHA-256 1f44fc383f303c2f6a5d33ac220a831e646eda2bb51cdf14a0e7db2d1c00b810. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared22.indexed_chunk00_checked :
    pairIndexedWitnessesPrefixBool smallPairA_22 smallPairB_22 anchorRoot
      (10^1100) smallPairClosure_22 64
      (witnesses.drop 0) (destinations.drop 0) = true := by sorry

end D1Bound5.PairGraphPrepared22
end
