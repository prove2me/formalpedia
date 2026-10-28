-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared36_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared36.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:06:59.275346+00:00
-- url     : https://prove2.me/theorems/26bdedcc-e30d-4795-8026-de3a3967f592
-- title:
--   Pair Light Closure Prepared36 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared36.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter36.lean, lines 17-29, SHA-256 1a9882a5e30534020908a86544947ccf8f3da2879be5b375995446cdd2930f59. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData36_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared36.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_36 smallPairB_36 PairGraphPrepared36.anchorRoot
      (10^1100) smallPairClosure_36 PairGraphPrepared36.witnesses PairGraphPrepared36.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared36
end
