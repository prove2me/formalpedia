-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared24_indexed_chunk04_checked
-- name    : D1Bound5.PairGraphPrepared24.indexed_chunk04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:21.815174+00:00
-- url     : https://prove2.me/theorems/9b9dd56e-5a84-41cc-b359-8808323d5b02
-- title:
--   Indexed mutation-closure certificate for prepared pair 24
-- statement:
--   For prepared pair 24, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure24Chunk04.lean, lines 9-14, SHA-256 89c8e85ef8b81f0bc44a96b7bc98dcac32d0efb432223d5e5d253728dbfd15e1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared24.indexed_chunk04_checked :
    pairIndexedWitnessesPrefixBool smallPairA_24 smallPairB_24 anchorRoot
      (10^1100) smallPairClosure_24 64
      (witnesses.drop 256) (destinations.drop 256) = true := by sorry

end D1Bound5.PairGraphPrepared24
end
