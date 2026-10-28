-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared6.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:46.022245+00:00
-- url     : https://prove2.me/theorems/4b995d4c-ee71-48fc-95b9-15af95f4fbc1
-- title:
--   Pair Light Closure Prepared6 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared6.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter6.lean, lines 17-29, SHA-256 3bc9090e96edc7c62853a7dae56534f9ddc63473766945ac647cc9e4f2c93c73. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData6_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData6_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared6.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_6 smallPairB_6 PairGraphPrepared6.anchorRoot
      (10^1100) smallPairClosure_6 PairGraphPrepared6.witnesses PairGraphPrepared6.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared6
end
