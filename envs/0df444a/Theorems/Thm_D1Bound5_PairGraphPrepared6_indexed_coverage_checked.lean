-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared6_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared6.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:37.247913+00:00
-- url     : https://prove2.me/theorems/c3d8cf71-9f9e-49f9-aa9a-54305bf2d98b
-- title:
--   Pair Graph Prepared6 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared6.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure6Coverage.lean, lines 9-29, SHA-256 37c8a6a440645519ca0b8e717de16e3409bcb5685ea6a39b615878c68896045e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData6_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData6_Definitions_003

section
namespace D1Bound5.PairGraphPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared6.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_6 * smallPairB_6 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_6) = true := by sorry

end D1Bound5.PairGraphPrepared6
end
