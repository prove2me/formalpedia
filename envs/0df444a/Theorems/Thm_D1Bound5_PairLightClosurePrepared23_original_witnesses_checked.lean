-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared23_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared23.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:11:58.367916+00:00
-- url     : https://prove2.me/theorems/0f6e1095-47cf-47c5-b33e-9116209f6f2f
-- title:
--   Pair Light Closure Prepared23 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared23.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter23.lean, lines 17-29, SHA-256 aa3baffa298df809147af75acff4c2890214a0225045d7bef5f41b4852ac1439. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData23_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData23_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared23.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_23 smallPairB_23 PairGraphPrepared23.anchorRoot
      (10^1100) smallPairClosure_23 PairGraphPrepared23.witnesses PairGraphPrepared23.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared23
end
