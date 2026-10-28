-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_chunk07_part03_checked
-- name    : D1Bound5.PairGraphPrepared3.indexed_chunk07_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:12.951677+00:00
-- url     : https://prove2.me/theorems/c7f8bbbf-3daf-4d54-9b6e-4b6fc0dbfc9b
-- title:
--   Indexed mutation-closure certificate for prepared pair 3, part 3
-- statement:
--   For prepared pair 3, part 3, the indexed closure certificate succeeds for at most `16` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure3Chunk07Part03.lean, lines 9-14, SHA-256 84f6a5e000a95290ef4d6b515868508112fa9dbfe3aca625faa2acbbf03d0931. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_003

section
namespace D1Bound5.PairGraphPrepared3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared3.indexed_chunk07_part03_checked :
    pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot
      (10^1100) smallPairClosure_3 16
      (witnesses.drop 496) (destinations.drop 496) = true := by sorry

end D1Bound5.PairGraphPrepared3
end
