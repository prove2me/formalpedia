-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared33_indexed_chunk01_checked
-- name    : D1Bound5.PairGraphPrepared33.indexed_chunk01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:02.342172+00:00
-- url     : https://prove2.me/theorems/98609f43-a8e7-4058-b221-145597c09111
-- title:
--   Indexed mutation-closure certificate for prepared pair 33
-- statement:
--   For prepared pair 33, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure33Chunk01.lean, lines 9-14, SHA-256 702c6114fc2ef004cf0a459b885b7ba9659f032ec2924ca046e6d3662f0b2440. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData33_Definitions_003

section
namespace D1Bound5.PairGraphPrepared33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared33.indexed_chunk01_checked :
    pairIndexedWitnessesPrefixBool smallPairA_33 smallPairB_33 anchorRoot
      (10^1100) smallPairClosure_33 128
      (witnesses.drop 128) (destinations.drop 128) = true := by sorry

end D1Bound5.PairGraphPrepared33
end
