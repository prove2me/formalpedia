-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_06_part0_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_chunk128_06_part0_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:26.617001+00:00
-- url     : https://prove2.me/theorems/acbe825d-975d-496f-aed5-ecca7cdcd27f
-- title:
--   Indexed mutation-closure certificate for prepared pair 26, part 0
-- statement:
--   For prepared pair 26, part 0, the indexed closure certificate succeeds for at most `32` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Original global vertex list; exactly 32 aligned witness/destination rows.
-- source:
--   D1Bound5/SmallPairGraphClosure26Chunk128_06Part0.lean, lines 9-14, SHA-256 26d39f5a60bf211462c3a064a5d759377360c793bc442c4f0d8ecd437ccf2ce0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared26.indexed_chunk128_06_part0_checked :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 32
      (witnesses.drop 768) (destinations.drop 768) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
