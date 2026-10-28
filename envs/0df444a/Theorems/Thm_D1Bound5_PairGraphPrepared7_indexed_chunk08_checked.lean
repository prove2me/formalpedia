-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk08_checked
-- name    : D1Bound5.PairGraphPrepared7.indexed_chunk08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:41.700924+00:00
-- url     : https://prove2.me/theorems/45c211fd-09fd-4b7f-9fae-5771802981b1
-- title:
--   Indexed mutation-closure certificate for prepared pair 7
-- statement:
--   For prepared pair 7, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure7Chunk08.lean, lines 9-14, SHA-256 437b6a56bed4b6f94b26963ae102a5ca981cb246d52fe850a2e52a3f5ae3508f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared7.indexed_chunk08_checked :
    pairIndexedWitnessesPrefixBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 64
      (witnesses.drop 512) (destinations.drop 512) = true := by sorry

end D1Bound5.PairGraphPrepared7
end
