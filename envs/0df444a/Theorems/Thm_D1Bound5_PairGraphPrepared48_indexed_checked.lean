-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared48_indexed_checked
-- name    : D1Bound5.PairGraphPrepared48.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:11:59.60551+00:00
-- url     : https://prove2.me/theorems/44674933-4026-4be0-8081-5145a7f1840e
-- title:
--   Pair Graph Prepared48 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared48.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure48.lean, lines 15-72, SHA-256 198676a6be372a21196ef6cfa12f60b7daffa7cfb63ec70651488a558130e6f8. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared48

theorem _root_.D1Bound5.PairGraphPrepared48.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_48 smallPairB_48 anchorRoot
      (10^1100) smallPairClosure_48 witnesses destinations = true := by sorry



end D1Bound5
end
