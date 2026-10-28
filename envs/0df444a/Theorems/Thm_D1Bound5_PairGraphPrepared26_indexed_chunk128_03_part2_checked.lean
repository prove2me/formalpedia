-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_03_part2_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_chunk128_03_part2_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:32.299979+00:00
-- url     : https://prove2.me/theorems/5324cdfa-b34c-4dcb-b532-42578a0cc704
-- title:
--   Indexed mutation-closure certificate for prepared pair 26, part 2
-- statement:
--   For prepared pair 26, part 2, the indexed closure certificate succeeds for at most `32` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Original global vertex list; exactly 32 aligned witness/destination rows.
-- source:
--   D1Bound5/SmallPairGraphClosure26Chunk128_03Part2.lean, lines 9-14, SHA-256 c5f68bf3219d00d1a473d62f571e156f8ccc21f89aafc57e3c179b665f5a48bb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003

section
namespace D1Bound5.PairGraphPrepared26
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared26.indexed_chunk128_03_part2_checked :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 32
      (witnesses.drop 448) (destinations.drop 448) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
