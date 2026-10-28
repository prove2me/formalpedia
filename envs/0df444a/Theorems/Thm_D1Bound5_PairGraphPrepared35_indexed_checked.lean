-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared35_indexed_checked
-- name    : D1Bound5.PairGraphPrepared35.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:12:19.41553+00:00
-- url     : https://prove2.me/theorems/ea3bb53d-3d3a-45b8-b64a-630d78872ba8
-- title:
--   Pair Graph Prepared35 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared35.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure35.lean, lines 15-72, SHA-256 22608355961fbffff98fd250386249b77e461b187afe41754d5d52c980214de5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData35_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared35

theorem _root_.D1Bound5.PairGraphPrepared35.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_35 smallPairB_35 anchorRoot
      (10^1100) smallPairClosure_35 witnesses destinations = true := by sorry



end D1Bound5
end
