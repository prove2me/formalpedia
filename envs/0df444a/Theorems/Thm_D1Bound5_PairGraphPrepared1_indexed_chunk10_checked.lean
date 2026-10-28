-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared1_indexed_chunk10_checked
-- name    : D1Bound5.PairGraphPrepared1.indexed_chunk10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:11.890346+00:00
-- url     : https://prove2.me/theorems/80742c82-bab1-4fed-af24-786aba97f432
-- title:
--   Indexed mutation-closure certificate for prepared pair 1
-- statement:
--   For prepared pair 1, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure1Chunk10.lean, lines 9-14, SHA-256 2772268a2a45d0ca6fcf626a195c3fb49f2f942d2d5e47bcd9df054b07d890c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs1_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData1_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData1_Definitions_003

section
namespace D1Bound5.PairGraphPrepared1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared1.indexed_chunk10_checked :
    pairIndexedWitnessesPrefixBool smallPairA_1 smallPairB_1 anchorRoot
      (10^1100) smallPairClosure_1 64
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairGraphPrepared1
end
