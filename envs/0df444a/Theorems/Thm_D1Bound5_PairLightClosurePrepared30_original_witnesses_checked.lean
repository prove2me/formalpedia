-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_original_witnesses_checked
-- name    : D1Bound5.PairLightClosurePrepared30.original_witnesses_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:08:22.587659+00:00
-- url     : https://prove2.me/theorems/3553fadd-4278-4b8c-a0af-db2b8bbe77db
-- title:
--   Pair Light Closure Prepared30 — original witnesses checked
-- statement:
--   Auxiliary result `PairLightClosurePrepared30.original_witnesses_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairPureClosureAdapter30.lean, lines 17-29, SHA-256 0663dcbb743c1c4afa79c329cdb332aaf79c607e181d814a4bda4a0c166ffc5d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData30_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData30_Definitions_003

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.D1Bound5.PairLightClosurePrepared30.original_witnesses_checked :
    pairIndexedWitnessesCheckedBool smallPairA_30 smallPairB_30 PairGraphPrepared30.anchorRoot
      (10^1100) smallPairClosure_30 PairGraphPrepared30.witnesses PairGraphPrepared30.destinations = true := by sorry



end D1Bound5.PairLightClosurePrepared30
end
