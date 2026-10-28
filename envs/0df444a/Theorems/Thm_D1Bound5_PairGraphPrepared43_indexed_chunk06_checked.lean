-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared43_indexed_chunk06_checked
-- name    : D1Bound5.PairGraphPrepared43.indexed_chunk06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:21.674326+00:00
-- url     : https://prove2.me/theorems/879b7c50-0207-4b64-8023-f37b4455409e
-- title:
--   Indexed mutation-closure certificate for prepared pair 43
-- statement:
--   For prepared pair 43, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both mutation signs use the complete original destination vertex list.
-- source:
--   D1Bound5/SmallPairGraphClosure43Chunk06.lean, lines 9-14, SHA-256 4821a116837b3a389b286965d24958dd5d783f71db83d092b8dc86391a2292ec. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData43_Definitions_003

section
namespace D1Bound5.PairGraphPrepared43
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared43.indexed_chunk06_checked :
    pairIndexedWitnessesPrefixBool smallPairA_43 smallPairB_43 anchorRoot
      (10^1100) smallPairClosure_43 64
      (witnesses.drop 384) (destinations.drop 384) = true := by sorry

end D1Bound5.PairGraphPrepared43
end
