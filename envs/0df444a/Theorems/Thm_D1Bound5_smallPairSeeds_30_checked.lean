-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_30_checked
-- name    : D1Bound5.smallPairSeeds_30_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:14.729992+00:00
-- url     : https://prove2.me/theorems/087df120-5530-4d4c-8c61-ec23b5e5f3e0
-- title:
--   Small Pair Seeds 30 checked
-- statement:
--   Auxiliary result `smallPairSeeds_30_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic30.lean, lines 8-11, SHA-256 2fd138ebe6b70d105e7a5c6395352b6efb6556641c47c26fd5fbea02b0f5d469. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_30_checked :
    pairSeedsCoveredBool smallPairA_30 smallPairB_30
      seedRootDisk_1_1 smallPairClosure_30 = true := by sorry





end D1Bound5
end
