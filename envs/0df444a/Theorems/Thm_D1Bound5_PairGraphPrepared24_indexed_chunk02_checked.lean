-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared24_indexed_chunk02_checked
-- name    : D1Bound5.PairGraphPrepared24.indexed_chunk02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:19.360288+00:00
-- url     : https://prove2.me/theorems/cec3fb17-a8c1-48af-82b4-652ccc99608d
-- title:
--   Indexed mutation-closure certificate for prepared pair 24
-- statement:
--   For prepared pair 24, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure24Chunk02.lean, lines 9-14, SHA-256 afdeb3456db2664058a79065441288def2b04d2faeb0a8079e777013a5b795db. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_003

section
namespace D1Bound5.PairGraphPrepared24
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared24.indexed_chunk02_checked :
    pairIndexedWitnessesPrefixBool smallPairA_24 smallPairB_24 anchorRoot
      (10^1100) smallPairClosure_24 64
      (witnesses.drop 128) (destinations.drop 128) = true := by sorry

end D1Bound5.PairGraphPrepared24
end
