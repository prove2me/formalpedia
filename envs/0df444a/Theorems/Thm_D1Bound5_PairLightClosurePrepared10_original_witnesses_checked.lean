-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared10_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared10.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:03:03.84865+00:00
-- url     : https://prove2.me/theorems/f374e622-97e2-44eb-8523-fbd26a5b3cc2
-- title:
--   Pair Light Closure Prepared10 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared10.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter10.lean, lines 17-29, SHA-256 8ebc95f71903998431bbcbe3ae517e2e33f29287c9f7fd370e0385e1ae67a1e8. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData10_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared10.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_10 smallPairB_10 PairGraphPrepared10.anchorRoot
      (10^1100) smallPairClosure_10 PairGraphPrepared10.witnesses PairGraphPrepared10.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared10
end
