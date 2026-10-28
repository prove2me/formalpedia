-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_32_checked
-- name    : D1Bound5.smallPairSeeds_32_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:24:56.865771+00:00
-- url     : https://prove2.me/theorems/d541eb34-aa1b-469c-9f9c-abb63582f5a9
-- title:
--   Small Pair Seeds 32 checked
-- statement:
--   Auxiliary result `smallPairSeeds_32_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic32.lean, lines 9-12, SHA-256 2cdfb46191da8d0a668035c89b1e4ccd361c01f01417759e813632466acc7296. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_32_checked :
    pairSeedsCoveredBool smallPairA_32 smallPairB_32
      seedRootDisk_0_6 smallPairClosure_32 = true := by sorry





end D1Bound5
end
