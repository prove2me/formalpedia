-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_14_checked
-- name    : D1Bound5.smallPairSeeds_14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:16.799949+00:00
-- url     : https://prove2.me/theorems/73282131-6b27-4c46-b712-5aecb073be1f
-- title:
--   Small Pair Seeds 14 checked
-- statement:
--   Auxiliary result `smallPairSeeds_14_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic14.lean, lines 8-11, SHA-256 ac7f4a5c9cf85b8d8231743af796775688a2c56128969c9064080f6e6520913a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_14_checked :
    pairSeedsCoveredBool smallPairA_14 smallPairB_14
      seedRootDisk_0_2 smallPairClosure_14 = true := by sorry





end D1Bound5
end
