-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_09_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_chunk128_09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:31.325944+00:00
-- url     : https://prove2.me/theorems/0062b426-4509-4c36-b01a-1956a2510926
-- title:
--   Indexed mutation-closure certificate for prepared pair 26
-- statement:
--   For prepared pair 26, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs and original global destination indices are preserved.
-- source:
--   D1Bound5/SmallPairGraphClosure26Chunk128_09.lean, lines 9-14, SHA-256 2335547f2059cb82b55d236695ea22ceec0399b36a2c1ad0c72c592a75e65028. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared26.indexed_chunk128_09_checked :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 128
      (witnesses.drop 1152) (destinations.drop 1152) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
