-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_tail128_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_tail128_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:57.833996+00:00
-- url     : https://prove2.me/theorems/18924a65-2eef-4a41-a840-f0722ab4a9d5
-- title:
--   Indexed mutation-closure certificate for prepared pair 26
-- statement:
--   For prepared pair 26, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Tail pilot: exactly rows 1397 through 1524, with original global destinations.
-- source:
--   D1Bound5/SmallPairGraphClosure26Tail128.lean, lines 9-14, SHA-256 7f607fdb3652398f73dbb17ab326f4d743a84e604cf2bb7ef0ffd80e19779c0e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared26.indexed_tail128_checked :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 128
      (witnesses.drop 1397) (destinations.drop 1397) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
