-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared35_indexed_chunk00_checked
-- name    : D1Bound5.PairGraphPrepared35.indexed_chunk00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:18.139321+00:00
-- url     : https://prove2.me/theorems/cb0ef3aa-abb3-40fd-8f15-fb6a31c66130
-- title:
--   Indexed mutation-closure certificate for prepared pair 35
-- statement:
--   For prepared pair 35, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure35Chunk00.lean, lines 9-14, SHA-256 148f1f71a561a0154dfd177a994417ac6d7b492a47477f1a136ad75d567ff505. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData35_Definitions_003

section
namespace D1Bound5.PairGraphPrepared35
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared35.indexed_chunk00_checked :
    pairIndexedWitnessesPrefixBool smallPairA_35 smallPairB_35 anchorRoot
      (10^1100) smallPairClosure_35 128
      (witnesses.drop 0) (destinations.drop 0) = true := by sorry

end D1Bound5.PairGraphPrepared35
end
