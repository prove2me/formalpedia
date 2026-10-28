-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk03_checked
-- name    : D1Bound5.PairGraphPrepared12.indexed_chunk03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:27.433673+00:00
-- url     : https://prove2.me/theorems/5ef55c8c-6f83-4cfe-ac17-76a0de0dec05
-- title:
--   Indexed mutation-closure certificate for prepared pair 12
-- statement:
--   For prepared pair 12, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure12Chunk03.lean, lines 9-14, SHA-256 0e406d98b9ce4a1e81d22189036fc620afe6239301446886ae8b4a2f4015d04a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData12_Definitions

section
namespace D1Bound5.PairGraphPrepared12
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared12.indexed_chunk03_checked :
    pairIndexedWitnessesPrefixBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 128
      (witnesses.drop 384) (destinations.drop 384) = true := by sorry

end D1Bound5.PairGraphPrepared12
end
