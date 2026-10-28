-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk00_part01_checked
-- name    : D1Bound5.PairGraphPrepared12.indexed_chunk00_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:06.813984+00:00
-- url     : https://prove2.me/theorems/95a494e9-1b22-4560-a9f6-13551fcd9a94
-- title:
--   Indexed mutation-closure certificate for prepared pair 12, part 1
-- statement:
--   For prepared pair 12, part 1, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Original rows 64 through 127, both mutation signs and the full destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure12Chunk00Part01.lean, lines 9-14, SHA-256 fda93fbe40ae595b5b8e5c3d29cad296ea05c73192a67c2a417e6e5475e3cad9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairGraphPrepared12.indexed_chunk00_part01_checked :
    pairIndexedWitnessesPrefixBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 64
      (witnesses.drop 64) (destinations.drop 64) = true := by sorry

end D1Bound5.PairGraphPrepared12
end
