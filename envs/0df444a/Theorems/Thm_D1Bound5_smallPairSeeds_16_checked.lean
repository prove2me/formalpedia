-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_16_checked
-- name    : D1Bound5.smallPairSeeds_16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:23:12.050923+00:00
-- url     : https://prove2.me/theorems/00fdbe0a-c1ed-4eef-a8c9-cb9c6b8ee987
-- title:
--   Small Pair Seeds 16 checked
-- statement:
--   Auxiliary result `smallPairSeeds_16_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic16.lean, lines 8-11, SHA-256 bd98f697bcf6d72c3084f4bb93b5d03975a38ffeff8bbcce40f798c8c7e817f6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs16_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_16_checked :
    pairSeedsCoveredBool smallPairA_16 smallPairB_16
      seedRootDisk_0_2 smallPairClosure_16 = true := by sorry





end D1Bound5
end
