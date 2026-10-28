-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk00_checked
-- name    : D1Bound5.PairGraphPrepared7.indexed_chunk00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:44.131332+00:00
-- url     : https://prove2.me/theorems/25ad4088-cf4f-4d13-9e61-f28de00e8c92
-- title:
--   Indexed mutation-closure certificate for prepared pair 7
-- statement:
--   For prepared pair 7, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure7Chunk00.lean, lines 9-14, SHA-256 6768acf118e478e840ad5076a5031afb34a977b228445a91f189223a7e452a9d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData7_Definitions_003

section
namespace D1Bound5.PairGraphPrepared7
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared7.indexed_chunk00_checked :
    pairIndexedWitnessesPrefixBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 64
      (witnesses.drop 0) (destinations.drop 0) = true := by sorry

end D1Bound5.PairGraphPrepared7
end
