-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared21.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:43.546529+00:00
-- url     : https://prove2.me/theorems/fb5b34fa-5f7d-4f57-8e3f-673b4d49b35f
-- title:
--   Pair Light Closure Prepared21 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared21.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter21.lean, lines 17-29, SHA-256 d019c6a5cd4c180ae47f8f8714d34bf27f8ba18733f6e843a35077cc5ffca2a3. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData21_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared21.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_21 smallPairB_21 PairGraphPrepared21.anchorRoot
      (10^1100) smallPairClosure_21 PairGraphPrepared21.witnesses PairGraphPrepared21.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared21
end
