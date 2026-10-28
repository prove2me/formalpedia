-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_17_checked
-- name    : D1Bound5.smallPairSeeds_17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:29.206758+00:00
-- url     : https://prove2.me/theorems/2e84e536-4134-4088-b259-30efb085c32b
-- title:
--   Small Pair Seeds 17 checked
-- statement:
--   Auxiliary result `smallPairSeeds_17_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic17.lean, lines 8-11, SHA-256 c5ad7a04be55cfcfdd22f3a74ab3f5e3ef667ed0f85cea269e060f25883ed011. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_17_checked :
    pairSeedsCoveredBool smallPairA_17 smallPairB_17
      seedRootDisk_0_2 smallPairClosure_17 = true := by sorry





end D1Bound5
end
