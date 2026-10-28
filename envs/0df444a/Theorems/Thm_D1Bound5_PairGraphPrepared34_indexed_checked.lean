-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared34_indexed_checked
-- name    : D1Bound5.PairGraphPrepared34.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:19:43.643993+00:00
-- url     : https://prove2.me/theorems/c6db7293-208d-4775-900f-163388d2e4d5
-- title:
--   Pair Graph Prepared34 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared34.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure34.lean, lines 10-13, SHA-256 a5f83b9e9c8233fc7e1eafda5a5ecb640388506da389699f4913e630e946b9f2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData34_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared34

theorem _root_.D1Bound5.PairGraphPrepared34.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_34 smallPairB_34 anchorRoot
      (10^1100) smallPairClosure_34 witnesses destinations = true := by sorry



end D1Bound5
end
