-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared25_indexed_chunk03_checked
-- name    : D1Bound5.PairGraphPrepared25.indexed_chunk03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:52.521331+00:00
-- url     : https://prove2.me/theorems/430cfed3-369d-4ddf-9ee9-10f79f0d9255
-- title:
--   Indexed mutation-closure certificate for prepared pair 25
-- statement:
--   For prepared pair 25, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure25Chunk03.lean, lines 9-14, SHA-256 fbc0f49942b8af5216a5d54ba40545860d5a4155b27fb1367672669e48d562e9. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData25_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData25_Definitions_003

section
namespace D1Bound5.PairGraphPrepared25
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared25.indexed_chunk03_checked :
    pairIndexedWitnessesPrefixBool smallPairA_25 smallPairB_25 anchorRoot
      (10^1100) smallPairClosure_25 64
      (witnesses.drop 192) (destinations.drop 192) = true := by sorry

end D1Bound5.PairGraphPrepared25
end
