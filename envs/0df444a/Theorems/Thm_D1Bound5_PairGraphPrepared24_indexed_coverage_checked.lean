-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared24_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared24.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:33:19.891278+00:00
-- url     : https://prove2.me/theorems/6fe24c4e-884b-4ffc-8ec6-3e5e487a9014
-- title:
--   Pair Graph Prepared24 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared24.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure24Coverage.lean, lines 9-29, SHA-256 78ea689420bdb8456d12fa898e8e0b7a4f5a3e4fe101a2acb707789fd0fec859. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
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

theorem _root_.D1Bound5.PairGraphPrepared24.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_24 * smallPairB_24 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_24) = true := by sorry

end D1Bound5.PairGraphPrepared24
end
