-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk10_checked
-- name    : D1Bound5.PairGraphPrepared37.indexed_chunk10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:38.876989+00:00
-- url     : https://prove2.me/theorems/7ab01df7-f693-47b0-9304-a28262f398e5
-- title:
--   Indexed mutation-closure certificate for prepared pair 37
-- statement:
--   For prepared pair 37, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure37Chunk10.lean, lines 9-14, SHA-256 9e3143e28e92c26631c92d99dc7ee35c83cd9a648dd88b713b56b24fb0b93755. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData37_Definitions_003

section
namespace D1Bound5.PairGraphPrepared37
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared37.indexed_chunk10_checked :
    pairIndexedWitnessesPrefixBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 64
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairGraphPrepared37
end
