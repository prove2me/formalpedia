-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_chunk07_part01_checked
-- name    : D1Bound5.PairGraphPrepared3.indexed_chunk07_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:29.401525+00:00
-- url     : https://prove2.me/theorems/c20dd10b-1df8-42eb-86d5-e960bb3f5302
-- title:
--   Indexed mutation-closure certificate for prepared pair 3, part 1
-- statement:
--   For prepared pair 3, part 1, the indexed closure certificate succeeds for at most `16` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure3Chunk07Part01.lean, lines 9-14, SHA-256 efc50ad9806129555e447d418b76ed0c80c779ecb10e42ab3d0eccef78283641. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_003

section
namespace D1Bound5.PairGraphPrepared3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared3.indexed_chunk07_part01_checked :
    pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot
      (10^1100) smallPairClosure_3 16
      (witnesses.drop 464) (destinations.drop 464) = true := by sorry

end D1Bound5.PairGraphPrepared3
end
