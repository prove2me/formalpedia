-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared39_indexed_chunk14_checked
-- name    : D1Bound5.PairGraphPrepared39.indexed_chunk14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:49.042118+00:00
-- url     : https://prove2.me/theorems/0b993274-cd4e-4b69-84f3-95ea68ae3544
-- title:
--   Indexed mutation-closure certificate for prepared pair 39
-- statement:
--   For prepared pair 39, the indexed closure certificate succeeds for at most `19` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure39Chunk14.lean, lines 9-14, SHA-256 25c12e3dea87a3deacfc7dbf8ebd68c96a02eed9fa24f9f3eba74bb3553740dd. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData39_Definitions_003

section
namespace D1Bound5.PairGraphPrepared39
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared39.indexed_chunk14_checked :
    pairIndexedWitnessesPrefixBool smallPairA_39 smallPairB_39 anchorRoot
      (10^1100) smallPairClosure_39 19
      (witnesses.drop 896) (destinations.drop 896) = true := by sorry

end D1Bound5.PairGraphPrepared39
end
