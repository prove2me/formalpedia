-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared46_indexed_chunk01_checked
-- name    : D1Bound5.PairGraphPrepared46.indexed_chunk01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:59.303635+00:00
-- url     : https://prove2.me/theorems/2272b2a8-b3c2-44d4-a4fe-22b1f7ac2483
-- title:
--   Indexed mutation-closure certificate for prepared pair 46
-- statement:
--   For prepared pair 46, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure46Chunk01.lean, lines 9-14, SHA-256 6f4008e4e922c0e12bb09bda650b1e661f74071c3f32321055ba16fec15df52b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs46_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData46_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData46_Definitions_003

section
namespace D1Bound5.PairGraphPrepared46
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared46.indexed_chunk01_checked :
    pairIndexedWitnessesPrefixBool smallPairA_46 smallPairB_46 anchorRoot
      (10^1100) smallPairClosure_46 64
      (witnesses.drop 64) (destinations.drop 64) = true := by sorry

end D1Bound5.PairGraphPrepared46
end
