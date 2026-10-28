-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_7_checked
-- name    : D1Bound5.smallPairSeeds_7_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:14.328393+00:00
-- url     : https://prove2.me/theorems/4233609f-844f-44b4-a552-85607a02aafb
-- title:
--   Small Pair Seeds 7 checked
-- statement:
--   Auxiliary result `smallPairSeeds_7_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic7.lean, lines 8-11, SHA-256 0ef8f8f7ef4980a5fe56eb3d4d2cef1633b5b0a5f1a82e3a730cb933da8ef799. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_7_checked :
    pairSeedsCoveredBool smallPairA_7 smallPairB_7
      seedRootDisk_0_1 smallPairClosure_7 = true := by sorry





end D1Bound5
end
