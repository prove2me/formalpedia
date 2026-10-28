-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_40_checked
-- name    : D1Bound5.smallPairSeeds_40_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:00.210012+00:00
-- url     : https://prove2.me/theorems/b7ff0628-16f0-465c-8685-507990650ca2
-- title:
--   Small Pair Seeds 40 checked
-- statement:
--   Auxiliary result `smallPairSeeds_40_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic40.lean, lines 8-11, SHA-256 3788dca3b4c8112730c195370cf0cf2fa35d87fc4dcb8d8c7333fa24d76ad539. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs40_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_40_checked :
    pairSeedsCoveredBool smallPairA_40 smallPairB_40
      seedRootDisk_1_2 smallPairClosure_40 = true := by sorry





end D1Bound5
end
