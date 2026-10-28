-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_33_checked
-- name    : D1Bound5.smallPairSeeds_33_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:17.733396+00:00
-- url     : https://prove2.me/theorems/51f06e2c-af9c-435a-9ef4-dfd271b8aabe
-- title:
--   Small Pair Seeds 33 checked
-- statement:
--   Auxiliary result `smallPairSeeds_33_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic33.lean, lines 8-11, SHA-256 1f432efb2f5cc7658a0f57027b5e82dd3b460a6557e5bfdfdd29431539469159. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs33_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_33_checked :
    pairSeedsCoveredBool smallPairA_33 smallPairB_33
      seedRootDisk_1_2 smallPairClosure_33 = true := by sorry





end D1Bound5
end
