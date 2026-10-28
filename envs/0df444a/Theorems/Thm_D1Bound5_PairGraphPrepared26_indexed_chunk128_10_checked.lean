-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_10_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_chunk128_10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:04.228216+00:00
-- url     : https://prove2.me/theorems/a3c739f6-6830-4c3f-8cac-1459158f6523
-- title:
--   Indexed mutation-closure certificate for prepared pair 26
-- statement:
--   For prepared pair 26, the indexed closure certificate succeeds for at most `117` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs and original global destination indices are preserved.
-- source:
--   D1Bound5/SmallPairGraphClosure26Chunk128_10.lean, lines 9-14, SHA-256 0666a66d5cb2115f5726978cfd7239a18bc01a1189ffeb00a0d7e69443bb6902. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared26.indexed_chunk128_10_checked :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 117
      (witnesses.drop 1280) (destinations.drop 1280) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
