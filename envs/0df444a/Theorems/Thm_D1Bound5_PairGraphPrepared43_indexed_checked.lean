-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared43_indexed_checked
-- name    : D1Bound5.PairGraphPrepared43.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:12:25.577079+00:00
-- url     : https://prove2.me/theorems/bde30e61-a1e9-4168-b8f7-f224a30490b0
-- title:
--   Pair Graph Prepared43 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared43.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure43.lean, lines 25-130, SHA-256 1699092b76086a40b2e0b1f7069344d65f09cb39b9f09ecca7ca7e72e1be2bb5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData43_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared43

theorem _root_.D1Bound5.PairGraphPrepared43.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_43 smallPairB_43 anchorRoot
      (10^1100) smallPairClosure_43 witnesses destinations = true := by sorry



end D1Bound5
end
