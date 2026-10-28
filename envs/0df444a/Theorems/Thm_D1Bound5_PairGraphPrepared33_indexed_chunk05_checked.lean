-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared33_indexed_chunk05_checked
-- name    : D1Bound5.PairGraphPrepared33.indexed_chunk05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:27.797002+00:00
-- url     : https://prove2.me/theorems/ed3c77d3-7e7a-4efe-bc9c-f53fe4b24ee8
-- title:
--   Indexed mutation-closure certificate for prepared pair 33
-- statement:
--   For prepared pair 33, the indexed closure certificate succeeds for at most `80` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure33Chunk05.lean, lines 9-14, SHA-256 fa10a3e47b0095347ae5301cc8d8df54e685b4a27d000a4f44cef312a8ea4c60. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared33.indexed_chunk05_checked :
    pairIndexedWitnessesPrefixBool smallPairA_33 smallPairB_33 anchorRoot
      (10^1100) smallPairClosure_33 80
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairGraphPrepared33
end
