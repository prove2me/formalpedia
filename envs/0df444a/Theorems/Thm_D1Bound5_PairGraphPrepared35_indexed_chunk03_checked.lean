-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared35_indexed_chunk03_checked
-- name    : D1Bound5.PairGraphPrepared35.indexed_chunk03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:01.117449+00:00
-- url     : https://prove2.me/theorems/3d1edac0-57ca-49d1-8b45-b43cb60315a0
-- title:
--   Indexed mutation-closure certificate for prepared pair 35
-- statement:
--   For prepared pair 35, the indexed closure certificate succeeds for at most `128` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Full original vertex list and both signs; only aligned row lists are sliced.
-- source:
--   D1Bound5/SmallPairGraphClosure35Chunk03.lean, lines 9-14, SHA-256 878bb6f44cca1fa5f3c69f589314fe0b5065e53c6cd97829125b844d675ff7cf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData35_Definitions_003

section
namespace D1Bound5.PairGraphPrepared35
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairGraphPrepared35.indexed_chunk03_checked :
    pairIndexedWitnessesPrefixBool smallPairA_35 smallPairB_35 anchorRoot
      (10^1100) smallPairClosure_35 128
      (witnesses.drop 384) (destinations.drop 384) = true := by sorry

end D1Bound5.PairGraphPrepared35
end
