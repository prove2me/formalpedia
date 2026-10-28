-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared19_indexed_chunk09_checked
-- name    : D1Bound5.PairGraphPrepared19.indexed_chunk09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:41:18.188615+00:00
-- url     : https://prove2.me/theorems/1c6b2276-f740-4a0b-b685-5b8cc5178b96
-- title:
--   Indexed mutation-closure certificate for prepared pair 19
-- statement:
--   For prepared pair 19, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure19Chunk09.lean, lines 9-14, SHA-256 bb7b2784ba38f656f32a7263edeb1b854a9d2e7a66c868ec8aded3e7ec0189b3. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData19_Definitions_003

section
namespace D1Bound5.PairGraphPrepared19
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared19.indexed_chunk09_checked :
    pairIndexedWitnessesPrefixBool smallPairA_19 smallPairB_19 anchorRoot
      (10^1100) smallPairClosure_19 64
      (witnesses.drop 576) (destinations.drop 576) = true := by sorry

end D1Bound5.PairGraphPrepared19
end
