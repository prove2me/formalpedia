-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared28.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:20:05.438301+00:00
-- url     : https://prove2.me/theorems/3e933c8e-d8e8-4e2a-9ef9-c17f5b2d49b3
-- title:
--   Pair Light Closure Prepared28 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared28.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter28.lean, lines 17-29, SHA-256 d9201a8656a6d59646eca9f2677b2d6eade0b4907b0942cb3d044c5c407e86af. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_SmallPairGraphInputs28_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs28_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData28_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData28_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared28
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared28.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_28 smallPairB_28 PairGraphPrepared28.anchorRoot
      (10^1100) smallPairClosure_28 PairGraphPrepared28.witnesses PairGraphPrepared28.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared28
end
