-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_checked
-- name    : D1Bound5.PairGraphPrepared3.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:04:50.324726+00:00
-- url     : https://prove2.me/theorems/a4e7c373-1bc6-4dfb-8439-f115998023bf
-- title:
--   Pair Graph Prepared3 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared3.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure3.lean, lines 22-109, SHA-256 6d15b89a2a116c6555da85d4cf9731182d4a4f7703df9c0da4d69aaff9714776. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared3

theorem _root_.D1Bound5.PairGraphPrepared3.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_3 smallPairB_3 anchorRoot
      (10^1100) smallPairClosure_3 witnesses destinations = true := by sorry



end D1Bound5
end
