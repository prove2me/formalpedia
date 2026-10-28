-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk13_checked
-- name    : D1Bound5.PairGraphPrepared5.indexed_chunk13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:24.231652+00:00
-- url     : https://prove2.me/theorems/a54cb6bf-c5c5-48e9-a26a-3a874e53fb94
-- title:
--   Indexed mutation-closure certificate for prepared pair 5
-- statement:
--   For prepared pair 5, the indexed closure certificate succeeds for at most `31` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure5Chunk13.lean, lines 9-14, SHA-256 d1c517c4b199b75183f1fb1af4a0d440f0c99ea5f681a6c120ea959873608f94. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData5_Definitions_003

section
namespace D1Bound5.PairGraphPrepared5
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared5.indexed_chunk13_checked :
    pairIndexedWitnessesPrefixBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 31
      (witnesses.drop 832) (destinations.drop 832) = true := by sorry

end D1Bound5.PairGraphPrepared5
end
