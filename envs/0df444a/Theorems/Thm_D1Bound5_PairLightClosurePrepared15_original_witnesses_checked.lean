-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared15_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared15.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:28:46.946564+00:00
-- url     : https://prove2.me/theorems/d8f1828e-c985-4367-ac74-9f46fac810f1
-- title:
--   Pair Light Closure Prepared15 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared15.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter15.lean, lines 17-29, SHA-256 9264e005a390c73265e0039a3168a31e61efb0001033af012999b3a2d4c8926e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData15_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared15.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_15 smallPairB_15 PairGraphPrepared15.anchorRoot
      (10^1100) smallPairClosure_15 PairGraphPrepared15.witnesses PairGraphPrepared15.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared15
end
