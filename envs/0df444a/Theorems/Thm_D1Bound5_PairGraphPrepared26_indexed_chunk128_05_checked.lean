-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_05_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_chunk128_05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:31.286987+00:00
-- url     : https://prove2.me/theorems/4f3a9289-c84a-4b20-859c-d3b7a6deded4
-- title:
--   Indexed mutation-closure certificate for prepared pair 26
-- statement:
--   For prepared pair 26, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs and original global destination indices are preserved.
-- source:
--   D1Bound5/SmallPairGraphClosure26Chunk128_05.lean, lines 9-14, SHA-256 09cf2be513a2f5fb01440fccd507548b02ad1ecbc15067f7a2e33e6f7d6b5dcf. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared26.indexed_chunk128_05_checked :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 128
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
