-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared24_indexed_chunk13_checked
-- name    : D1Bound5.PairGraphPrepared24.indexed_chunk13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:48.402376+00:00
-- url     : https://prove2.me/theorems/93bef476-6594-4ca2-8c23-1d89852181a6
-- title:
--   Indexed mutation-closure certificate for prepared pair 24
-- statement:
--   For prepared pair 24, the indexed closure certificate succeeds for at most `62` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure24Chunk13.lean, lines 9-14, SHA-256 2cce642e5b274bd61c2b5a5c07d5de72c404fde35f1078b58eb3cfd43d3f2b8d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_003

section
namespace D1Bound5.PairGraphPrepared24
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared24.indexed_chunk13_checked :
    pairIndexedWitnessesPrefixBool smallPairA_24 smallPairB_24 anchorRoot
      (10^1100) smallPairClosure_24 62
      (witnesses.drop 832) (destinations.drop 832) = true := by sorry

end D1Bound5.PairGraphPrepared24
end
